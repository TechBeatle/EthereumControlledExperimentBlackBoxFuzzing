# BSD 3-Clause License
#
# Copyright (c) 2016, 2017, The University of Sydney. All rights reserved.
#
# Redistribution and use in source and binary forms, with or without
# modification, are permitted provided that the following conditions are met:
#
# * Redistributions of source code must retain the above copyright notice, this
#   list of conditions and the following disclaimer.
#
# * Redistributions in binary form must reproduce the above copyright notice,
#   this list of conditions and the following disclaimer in the documentation
#   and/or other materials provided with the distribution.
#
# * Neither the name of the copyright holder nor the names of its
#   contributors may be used to endorse or promote products derived from
#   this software without specific prior written permission.
#
# THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
# AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
# IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
# DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE
# FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
# DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
# SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
# CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,
# OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
# OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

"""tac_cfg.py: Definitions of Three-Address Code operations and related
objects."""

import os
import copy
import logging
import typing as t

import networkx as nx

import src.blockparse as blockparse
import src.cfg as cfg
import src.evm_cfg as evm_cfg
import src.memtypes as mem
import src.opcodes as opcodes
import src.patterns as patterns
import src.settings as settings
from src.lattice import SubsetLatticeElement as ssle

from hashlib import sha256

POSTDOM_END_NODE = "END"
"""The name of the synthetic end node added for post-dominator calculations."""
UNRES_DEST = "?"
"""The name of the unresolved jump destination auxiliary node."""


class TACGraph(cfg.ControlFlowGraph):
    """
    A control flow graph holding Three-Address Code blocks and
    the edges between them.
    """

    def __init__(self, evm_blocks: t.Iterable[evm_cfg.EVMBasicBlock]):
        """
        Construct a TAC control flow graph from a given sequence of EVM blocks.
        Immediately after conversion, constants will be propagated and folded
        through arithmetic operations, and CFG edges will be connected up, wherever
        they can be inferred.

        Args:
          evm_blocks: an iterable of EVMBasicBlocks to convert into TAC form.
        """
        super().__init__()

        # Convert the input EVM blocks to TAC blocks.
        destack = Destackifier()

        self.blocks = [destack.convert_block(b) for b in evm_blocks]
        """The sequence of TACBasicBlocks contained in this graph."""
        for b in self.blocks:
            b.cfg = self

        self.root = next((b for b in self.blocks if b.entry == 0), None)
        """
        The root block of this CFG.
        The entry point will always be at index 0, if it exists.
        """

        self.split_node_succs = {}
        """
        A mapping from addresses to addresses storing all successors of a
        block at the time it was split. At merge time these edges can be restored.
        """

        self.function_extractor = None
        """
        A FunctionExtractor object, which encapsulates solidity functions
        and extraction logic.
        """

        # Propagate constants and add CFG edges.
        self.apply_operations()
        self.hook_up_jumps()

    @classmethod
    def from_dasm(cls, dasm: t.Iterable[str]) -> 'TACGraph':
        """
        Construct and return a TACGraph from the given EVM disassembly.

        Args:
          dasm: a sequence of disasm lines, as output from the
                ethereum `dasm` disassembler.
        """
        return cls(blockparse.EVMDasmParser(dasm).parse())

    @classmethod
    def from_bytecode(cls, bytecode: t.Iterable) -> 'TACGraph':
        """
        Construct and return a TACGraph from the given EVM bytecode.

        Args:
          bytecode: a sequence of EVM bytecode, either in a hexadecimal
            string format or a byte array.
        """
        bytecode = ''.join([l.strip() for l in bytecode if len(l.strip()) > 0])
        return cls(blockparse.EVMBytecodeParser(bytecode).parse())

    @property
    def tac_ops(self):
        for block in self.blocks:
            for op in block.tac_ops:
                yield op

    @property
    def last_op(self):
        return max((b.last_op for b in self.blocks),
                   key=lambda o: o.pc)

    @property
    def terminal_ops(self):
        terminals = [op for op in self.tac_ops if op.opcode.possibly_halts()]
        last_op = self.last_op
        if last_op not in terminals:
            return terminals + [last_op]
        return terminals

    def op_edge_list(self) -> t.Iterable[t.Tuple['TACOp', 'TACOp']]:
        """
        Returns:
          a list of the CFG's operation edges, with each edge in the form
          `(pred, succ)` where pred and succ are object references.
        """
        edges = []
        for block in self.blocks:
            intra_edges = list(zip(block.tac_ops[:-1], block.tac_ops[1:]))
            edges += intra_edges
            for succ in block.succs:
                edges.append((block.tac_ops[-1], succ.tac_ops[0]))
        return edges

    def nx_graph(self, op_edges=False) -> nx.DiGraph:
        """
        Return a networkx representation of this CFG.
        Nodes are labelled by their corresponding block's identifier.

        Args:
          op_edges: if true, return edges between instructions rather than blocks.
        """
        g = nx.DiGraph()

        if op_edges:
            g.add_nodes_from(hex(op.pc) for op in self.tac_ops)
            g.add_edges_from((hex(p.pc), hex(s.pc)) for p, s in self.op_edge_list())
            g.add_edges_from((hex(block.last_op.pc), UNRES_DEST)
                             for block in self.blocks if block.has_unresolved_jump)
        else:
            g.add_nodes_from(b.ident() for b in self.blocks)
            g.add_edges_from((p.ident(), s.ident()) for p, s in self.edge_list())
            g.add_edges_from((block.ident(), UNRES_DEST) for block in self.blocks
                             if block.has_unresolved_jump)
        return g

    def immediate_dominators(self, post: bool = False, op_edges=False) \
        -> t.Dict[str, str]:
        """
        Return the immediate dominator mapping of this graph.
        Each node is mapped to its unique immediately dominating node.
        This mapping defines a tree with the root being its own immediate dominator.

        Args:
          post: if true, return post-dominators instead, with an auxiliary node
                  END with edges from all terminal nodes in the CFG.
          op_edges: if true, return edges between instructions rather than blocks.

        Returns:
          dict: str -> str, maps from node identifiers to node identifiers.
        """
        nx_graph = self.nx_graph(op_edges).reverse() if post \
            else self.nx_graph(op_edges)

        # Logic here is not quite robust when op_edges is true, but correct
        # whenever there is a unique entry node, and no graph-splitting.
        start = POSTDOM_END_NODE if post else self.root.ident()

        if post:
            if op_edges:
                terminal_edges = [(POSTDOM_END_NODE, hex(op.pc))
                                  for op in self.terminal_ops]
            else:
                terminal_edges = [(POSTDOM_END_NODE, op.block.ident())
                                  for op in self.terminal_ops]
            nx_graph.add_node(POSTDOM_END_NODE)
            nx_graph.add_edges_from(terminal_edges)

        doms = nx.algorithms.dominance.immediate_dominators(nx_graph, start)
        idents = [b.ident() for b in self.blocks]

        if not op_edges:
            for d in [d for d in doms if d not in idents]:
                del doms[d]

        # TODO: determine whether to remove non-terminal END-postdominators
        #       and turn terminal ones into self-postdominators

        return doms

    def dominators(self, post: bool = False, op_edges=False) \
        -> t.Dict[str, t.Set[str]]:
        """
        Return the dominator mapping of this graph.
        Each block is mapped to the set of blocks that dominate it; its ancestors
        in the dominator tree.

        Args
          post: if true, return postdominators instead.
          op_edges: if true, return edges between instructions rather than blocks.

        Returns:
          dict: str -> [str], a map block identifiers to block identifiers.
        """

        idoms = self.immediate_dominators(post, op_edges)
        doms = {d: set() for d in idoms}

        for d in doms:
            prev = d
            while prev not in doms[d]:
                doms[d].add(prev)
                prev = idoms[prev]

        return doms

    def apply_operations(self, use_sets=False) -> None:
        """
        Propagate and fold constants through the arithmetic TAC instructions
        in this CFG.

        If use_sets is True, folding will also be done on Variables that
        possess multiple possible values, performing operations in all possible
        combinations of values.
        """
        for block in self.blocks:
            block.apply_operations(use_sets)

    def hook_up_stack_vars(self) -> None:
        """
        Replace all stack MetaVariables will be replaced with the actual
        variables they refer to.
        """
        for block in self.blocks:
            block.hook_up_stack_vars()

    def hook_up_def_site_jumps(self) -> None:
        """
        Add jumps to blocks with unresolved jumps if they can be inferred
        from the jump variable's definition sites.
        """
        for block in self.blocks:
            block.hook_up_def_site_jumps()

    def hook_up_jumps(self) -> bool:
        """
        Connect all edges in the graph that can be inferred given any constant
        values of jump destinations and conditions.
        Invalid jumps are replaced with THROW instructions.

        This is assumed to be performed after constant propagation and/or folding,
        since edges are deduced from constant-valued jumps.

        Note that the global mutate_jumps and generate_throws settings should
        likely be true only in the final iteration of a dataflow analysis, at which
        point as much jump destination information as possible has been propagated
        around. If these are used too early, they may prevent valid edges from
        being added later on.

        Returns:
            True iff any edges in the graph were modified.
        """

        # Hook up all jumps, modified will be true if any jump in the graph
        # was changed. Did not use any() and a generator due to lazy-eval,
        # which would be incorrect behaviour.
        modified = False
        for block in self.blocks:
            modified |= block.hook_up_jumps()
        return modified

    def add_missing_split_edges(self):
        """
        If this graph has had its nodes split, if new edges are inferred,
        we need to join them up to all copies of a node, but the split
        paths should remain separate, so only add such edges if parallel ones
        don't already exist on some split path.

        Returns true iff some new edge was added to the graph.
        """
        modified = False

        for pred_address in self.split_node_succs:
            preds = self.get_blocks_by_pc(pred_address)
            s_lists = [node.succs for node in preds]
            succs = set(s for s_list in s_lists for s in s_list)
            for succ in self.split_node_succs[pred_address]:
                if succ not in succs:
                    for pred in preds:
                        if not self.has_edge(pred, succ):
                            self.add_edge(pred, succ)
                            modified = True

        return modified

    def is_valid_jump_dest(self, pc: int) -> bool:
        """True iff the given program counter refers to a valid jumpdest."""
        ops = self.get_ops_by_pc(pc)
        return (len(ops) != 0) and any(op.opcode == opcodes.JUMPDEST for op in ops)

    def get_ops_by_pc(self, pc: int) -> 'TACOp':
        """Return the operations with the given program counter, if any exist."""
        ops = []

        for block in self.get_blocks_by_pc(pc):
            for op in block.tac_ops:
                if op.pc == pc:
                    ops.append(op)

        return ops

    def clone_ambiguous_jump_blocks(self) -> bool:
        """
        If block terminates in a jump with an ambiguous (but constrained)
        jump destination, then find its most recent ancestral confluence point
        and split the path of blocks between into parallel paths, one for each
        predecessor of the block at the confluence point.

        Returns:
            True iff some block was cloned.
        """

        split_occurred = False
        modified = True
        skip = set()

        while modified:
            modified = False

            for block in self.blocks:

                if not self.__split_block_is_splittable(block, skip):
                    continue

                # We satisfy the conditions for attempting a split.
                path = [block]
                curr_block = block
                cycle = False

                # Find the actual path to be split.
                while len(curr_block.preds) == 1:
                    curr_block = curr_block.preds[0]

                    if curr_block not in path:
                        path.append(curr_block)
                    else:
                        # We are in a cycle, break out
                        cycle = True
                        break

                path_preds = list(curr_block.preds)

                # If there's a cycle within the path, die
                # IDEA: See what happens if we copy these cycles
                if cycle or len(path_preds) == 0:
                    continue
                if any(pred in path for pred in path_preds):
                    continue

                # We have identified a splittable path, now split it

                # Remove the old path from the graph.
                skip |= self.__split_remove_path(path)
                # Note well that this deletion will remove all edges to successors
                # of elements of this path, so we can lose information.

                # Generate new paths from the old path, and hook them up properly.
                skip |= self.__split_copy_path(path, path_preds)

                modified = True
                split_occurred = True

        return split_occurred

    def __split_block_is_splittable(self, block, skip):
        """
        True when the given block satisfies the conditions for being the final node
        in a fissionable path. This will be the start point from which the path
        itself will be constructed, following CFG edges backwards until some
        ancestor with multiple predecessors is reached.
        """
        # Don't split on blocks we only just generated; some will
        # certainly satisfy the fission condition.
        if block in skip:
            return False

        # If the block does not end in a jump, don't start a split here.
        if block.last_op.opcode not in [opcodes.JUMP, opcodes.JUMPI]:
            return False

        # We will only split if there were actually multiple jump destinations
        # defined in multiple different ancestral blocks.
        dests = block.last_op.args[0].value
        if dests.is_const or dests.def_sites.is_const \
            or (dests.is_top and dests.def_sites.is_top):
            return False

        return True

    def __split_remove_path(self, path):
        """
        Resect the given path of nodes from the graph, and add its successors
        to the split_node_succs mapping in anticipation of the path's members
        being duplicated and reinserted into the graph.
        Return the set of blocks that need to be added to the skip list.
        """
        skip = set()
        for b in path:
            # Save the edges of each block in case they can't be re-inferred.
            # They will be added back in at a later stage.
            if b.entry not in self.split_node_succs:
                self.split_node_succs[b.entry] = [s for s in sorted(b.succs)]
            else:
                new_list = self.split_node_succs[b.entry]
                new_list += [s for s in sorted(b.succs) if s not in new_list]
                self.split_node_succs[b.entry] = new_list

            skip.add(b)
            self.remove_block(b)

        return skip

    def __split_copy_path(self, path, path_preds):
        """
        Duplicate the given path once for each block in path_preds,
        with each pred being the sole parent of the head of each duplicated path.
        Return the set of blocks that need to be added to the skip list.
        """
        # copy the path
        path_copies = [[copy.deepcopy(b) for b in path]
                       for _ in range(len(path_preds))]

        # Copy the nodes properly in the split node succs mapping.
        for i, b in enumerate(path):
            for a in self.split_node_succs:
                node_copies = [c[i] for c in path_copies]
                if b in self.split_node_succs[a]:
                    self.split_node_succs[a].remove(b)
                    self.split_node_succs[a] += node_copies

        # hook up each pred to a path individually.
        for i, p in enumerate(path_preds):
            self.add_edge(p, path_copies[i][-1])
            for b in path_copies[i]:
                b.ident_suffix += "_" + p.ident()

        # Connect the paths up within themselves
        for path_copy in path_copies:
            for i in range(len(path_copy) - 1):
                self.add_edge(path_copy[i + 1], path_copy[i])

        skip = set()
        # Add the new paths to the graph.
        for c in path_copies:
            for b in c:
                skip.add(b)
                self.add_block(b)

        return skip

    def merge_duplicate_blocks(self,
                               ignore_preds: bool = False,
                               ignore_succs: bool = False) -> None:
        """
        Blocks with the same addresses are merged if they have the same
        in and out edges.

        Input blocks will have their stacks joined, while pred and succ lists
        are the result of the the union of the input lists.

        It is assumed that the code of the duplicate blocks will be the same,
        which is to say that they can only differ by their entry/exit stacks,
        and their incident CFG edges.

        Args:
            ignore_preds: blocks will be merged even if their predecessors differ.
            ignore_succs: blocks will be merged even if their successors differ.
        """

        # Define an equivalence relation over basic blocks.
        # Blocks deemed equivalent by this function will be merged.
        def blocks_equal(a, b):
            if a.entry != b.entry:
                return False
            if not ignore_preds and set(a.preds) != set(b.preds):
                return False
            if not ignore_succs and set(a.succs) != set(b.succs):
                return False
            return True

        modified = True

        # We'll keep on merging until there's nothing left to be merged.
        # At present, the equivalence relation is such that all equivalent
        # blocks should be merged in one pass, but it may be necessary in future
        # to worry about new merge candidates being produced after merging.
        while modified:
            modified = False

            # A list of lists of blocks to be merged.
            groups = []

            # Group equivalent blocks together into lists.
            for block in self.blocks:
                grouped = False
                for group in groups:
                    if blocks_equal(block, group[0]):
                        grouped = True
                        group.append(block)
                        break
                if not grouped:
                    groups.append([block])

            # Ignore blocks that are in groups by themselves.
            groups = [g for g in groups if len(g) > 1]

            if len(groups) > 0:
                modified = True

            # Merge each group into a single new block.
            for i, group in enumerate(groups):

                # Join all stacks in merged blocks.
                entry_stack = mem.VariableStack.join_all([b.entry_stack for b in group])
                entry_stack.metafy()
                exit_stack = mem.VariableStack.join_all([b.exit_stack for b in group])
                exit_stack.metafy()

                # Collect all predecessors and successors of the merged blocks.
                preds = set()
                succs = set()
                for b in group:
                    preds |= set(b.preds)
                    succs |= set(b.succs)

                # Produce the disjunction of other informative fields within the group.
                symbolic_overflow = any([b.symbolic_overflow for b in group])
                has_unresolved_jump = any([b.has_unresolved_jump for b in group])

                # Construct the new merged block itself.
                # Its identifier will end in an identifying number unless its entry
                # address is unique in the graph.
                new_block = copy.deepcopy(group[0])
                new_block.entry_stack = entry_stack
                new_block.exit_stack = exit_stack
                new_block.preds = list(sorted(preds))
                new_block.succs = list(sorted(succs))
                new_block.ident_suffix = "_" + str(i)
                new_block.symbolic_overflow = symbolic_overflow
                new_block.has_unresolved_jump = has_unresolved_jump

                # Make sure block references inside ops and variables are redirected.
                new_block.reset_block_refs()

                # Add the new block to the graph and connect its edges up properly,
                # while also removing all merged blocks and incident edges.
                self.add_block(new_block)

                for pred in preds:
                    self.add_edge(pred, new_block)
                    for b in group:
                        self.remove_edge(pred, b)
                for succ in succs:
                    self.add_edge(new_block, succ)
                    for b in group:
                        self.remove_edge(b, succ)
                for b in group:
                    self.remove_block(b)

                # If this block no longer has any duplicates in the graph,
                # then everything it was split from has been merged.
                # It no longer needs an ident suffix to disambiguate it and its entry in
                # he split successors mapping can be removed, along with the edges
                # inferred from that mapping connected up.
                if len(self.get_blocks_by_pc(new_block.entry)) == 1:
                    new_block.ident_suffix = ""

                    for a in self.split_node_succs:
                        s_list = self.split_node_succs[a]
                        for g in [g for g in group if g in s_list]:
                            s_list.remove(g)

                    if new_block.entry in self.split_node_succs:
                        for succ in self.split_node_succs[new_block.entry]:
                            if succ not in new_block.succs:
                                new_block.succs.append(succ)
                        del self.split_node_succs[new_block.entry]

            # Recondition the graph, having merged everything.
            for block in self.blocks:
                block.build_entry_stack()
                block.build_exit_stack()
                block.hook_up_stack_vars()
                block.apply_operations()
                block.hook_up_jumps()

    def merge_contiguous(self, pred: 'TACBasicBlock', succ: 'TACBasicBlock') -> 'TACBasicBlock':
        """
        Merge two blocks in the cfg if they are contiguous.
        Pred should have a lower address than succ, and they should have
        zero out- and in-degree respectively.

        Args:
            pred: earlier block to merge
            succ: later block to merge

        Returns:
            The resulting merged block.
        """

        # Do not merge the blocks if they cannot be merged.
        if succ.entry != (pred.exit + 1) or len(pred.succs) != 0 or len(succ.preds) != 0:
            err_str = "Attempted to merge unmergeable blocks {} and {}.".format(pred.ident(), succ.ident())
            logging.error(err_str)
            raise RuntimeError(err_str)

        # Construct the merged block.
        tac_ops = pred.tac_ops + succ.tac_ops
        evm_ops = pred.evm_ops + succ.evm_ops
        delta_stack = pred.delta_stack.copy()
        delta_stack.pop_many(pred.delta_stack.empty_pops)
        delta_stack.push_many(reversed(succ.delta_stack.value))
        merged = TACBasicBlock(pred.entry, succ.exit,
                               tac_ops, evm_ops,
                               delta_stack, self)
        merged.entry_stack = pred.entry_stack.copy()
        merged.has_unresolved_jump = succ.has_unresolved_jump
        merged.ident_suffix = pred.ident_suffix + pred.ident_suffix

        # Update the CFG edges.
        self.add_block(merged)
        for b in pred.preds:
            self.add_edge(b, merged)
        for b in succ.succs:
            self.add_edge(merged, b)
        self.remove_block(pred)
        self.remove_block(succ)

        return merged

    def merge_unreachable_blocks(self, origin_addresses: t.Iterable[int] = [0]) \
        -> t.Iterable[t.Iterable['TACBasicBlock']]:
        """
        Merge all unreachable blocks with contiguous addresses into a single
        block. Will only merge blocks if they have no intervening edges.
        Assumes that blocks have unique entry and exit addresses.

        Args:
            origin_addresses: default value: [0], entry addresses, blocks
                              from which are unreachable to be merged.

        Returns:
            An iterable of the groups of blocks which were merged.
        """
        reached = self.transitive_closure(origin_addresses)

        # Sort the unreached ones for more-efficient merging.
        unreached = sorted([b for b in self.blocks if b not in reached], key=lambda b: b.entry)
        if len(unreached) == 0:
            return []

        # Collect the contiguous runs of blocks.
        groups = []
        group = [unreached[0]]
        for b in unreached[1:]:
            # Add the next block to the merge list only if
            # it is contiguous and has no incident edges.
            prev = group[-1]
            if b.entry == (prev.exit + 1) and len(prev.succs) == 0 and len(b.preds) == 0:
                group.append(b)
                continue

            # Singleton groups don't need to be merged
            if len(group) > 1:
                groups.append(group)

            # Start the next group
            group = [b]

        if len(group) > 1:
            groups.append(group)

        # Merge the blocks in each run.
        merged = []
        for g in groups:
            block = g[0]
            for n in g[1:]:
                block = self.merge_contiguous(block, n)
            merged.append(block)

        return groups

    def prop_vars_between_blocks(self) -> None:
        """
        If some entry stack variable is defined in exactly one place, fetch the
        appropriate variable from its source block and substitute it in, along with
        all occurrences of that stack variable in operations and the exit stack.
        """

        for block in self.blocks:
            for i in range(len(block.entry_stack)):
                stack = block.entry_stack
                if stack.value[i].def_sites.is_const:
                    # Fetch variable from def site.
                    location = next(iter(stack.value[i].def_sites))
                    old_var = stack.value[i]
                    new_var = None
                    for op in location.block.tac_ops:
                        if op.pc == location.pc:
                            new_var = op.lhs

                    # Reassign the entry stack position.
                    stack.value[i] = new_var

                    # Reassign exit stack occurrences
                    for j in range(len(block.exit_stack)):
                        if block.exit_stack.value[j] is old_var:
                            block.exit_stack.value[j] = new_var

                    # Reassign occurrences on RHS of operations
                    for o in block.tac_ops:
                        for j in range(len(o.args)):
                            if o.args[j].value is old_var:
                                o.args[j].var = new_var

    def make_stack_names_unique(self) -> None:
        """
        If two variables on the same entry stack share a name but are not the
        same variable, then make the names unique.
        The renaming will propagate through to all occurrences of that var.
        """

        for block in self.blocks:
            # Group up the variables by their names
            variables = sorted(block.entry_stack.value, key=lambda x: x.name)
            if len(variables) == 0:
                continue
            groups = [[variables[0]]]
            for i in range(len(variables))[1:]:
                v = variables[i]
                # When the var name in the name-sorted list changes, start a new group.
                if v.name != variables[i - 1].name:
                    groups.append([v])
                else:
                    # If the variable has already been processed, it only needs to
                    # be renamed once.
                    appeared = False
                    for prev_var in groups[-1]:
                        if v is prev_var:
                            appeared = True
                            break
                    if not appeared:
                        groups[-1].append(v)

            # Actually perform the renaming operation on any groups longer than 1
            for group in groups:
                if len(group) < 2:
                    continue
                for i in range(len(group)):
                    group[i].name += str(i)

    def extract_functions(self):
        """
        Attempt to extract solidity functions from this contract.
        Call this after having already called prop_vars_between_blocks() on cfg.
        """
        import src.function as function
        fe = function.FunctionExtractor(self)
        fe.extract()
        self.function_extractor = fe


class TACBasicBlock(evm_cfg.EVMBasicBlock):
    """
    A basic block containing both three-address code, and its
    equivalent EVM code, along with information about the transformation
    applied to the stack as a consequence of its execution.
    """

    def __init__(self, entry_pc: int, exit_pc: int,
                 tac_ops: t.List['TACOp'],
                 evm_ops: t.List[evm_cfg.EVMOp],
                 delta_stack: mem.VariableStack,
                 cfg=None):
        """
        Args:
          entry_pc: The pc of the first byte in the source EVM block
          exit_pc: The pc of the last byte in the source EVM block
          tac_ops: A sequence of TACOps whose execution is equivalent to the source
                   EVM code.
          evm_ops: the source EVM code.
          delta_stack: A stack describing the change in the stack state as a result
                       of running this block.
                       This stack contains the new items inhabiting the top of
                       stack after execution, along with the number of items
                       removed from the stack.
          cfg: The TACGraph to which this block belongs.

          Entry and exit variables should span the entire range of values enclosed
          in this block, taking care to note that the exit address may not be an
          instruction, but an argument of a PUSH.
          The range of pc values spanned by all blocks in a CFG should be a
          continuous range from 0 to the maximum value with no gaps between blocks.

          If the input stack state is known, obtain the exit stack state by
          popping off delta_stack.empty_pops items and add the delta_stack items
          to the top.
        """

        super().__init__(entry_pc, exit_pc, evm_ops)

        self.tac_ops = tac_ops
        """A sequence of TACOps whose execution is equivalent to the source EVM
           code"""

        self.delta_stack = delta_stack
        """
        A stack describing the stack state changes caused by running this block.
        MetaVariables named Sn symbolically denote the variable that was n places
        from the top of the stack at entry to this block.
        """

        self.entry_stack = mem.VariableStack()
        """Holds the complete stack state before execution of the block."""

        self.exit_stack = mem.VariableStack()
        """Holds the complete stack state after execution of the block."""

        self.symbolic_overflow = False
        """
        Indicates whether a symbolic stack overflow has occurred in dataflow
        analysis of this block.
        """

        self.cfg = cfg
        """The TACGraph to which this block belongs."""

    def __str__(self):
        super_str = super().__str__()
        op_seq = "\n".join(str(op) for op in self.tac_ops)
        entry_stack = "Entry stack: {}".format(str(self.entry_stack))
        stack_pops = "Stack pops: {}".format(self.delta_stack.empty_pops)
        stack_adds = "Stack additions: {}".format(str(self.delta_stack))
        exit_stack = "Exit stack: {}".format(str(self.exit_stack))
        return "\n".join([super_str, self._STR_SEP, op_seq, self._STR_SEP,
                          entry_stack, stack_pops, stack_adds, exit_stack])

    def accept(self, visitor: patterns.Visitor) -> None:
        """
        Accepts a visitor and visits itself and all TACOps in the block.

        Args:
          visitor: an instance of :obj:`patterns.Visitor` to accept.
        """
        super().accept(visitor)

        if visitor.can_visit(TACOp) or visitor.can_visit(TACAssignOp):
            for tac_op in self.tac_ops:
                visitor.visit(tac_op)

    def __deepcopy__(self, memodict={}):
        """Return a copy of this block."""

        new_block = TACBasicBlock(self.entry, self.exit,
                                  copy.deepcopy(self.tac_ops, memodict),
                                  [copy.copy(op) for op in self.evm_ops],
                                  copy.deepcopy(self.delta_stack, memodict))

        new_block.fallthrough = self.fallthrough
        new_block.has_unresolved_jump = self.has_unresolved_jump
        new_block.symbolic_overflow = self.symbolic_overflow
        new_block.entry_stack = copy.deepcopy(self.entry_stack, memodict)
        new_block.exit_stack = copy.deepcopy(self.exit_stack, memodict)
        new_block.preds = copy.copy(self.preds)
        new_block.succs = copy.copy(self.succs)
        new_block.ident_suffix = self.ident_suffix
        new_block.cfg = self.cfg

        new_block.reset_block_refs()

        return new_block

    @property
    def last_op(self) -> 'TACOp':
        """Return the last TAC operation in this block if it exists."""
        if len(self.tac_ops):
            return self.tac_ops[-1]
        return None

    @last_op.setter
    def last_op(self, op):
        """
        Set the last TAC operation in this block, if there is one.
        Append if one doesn't exist.
        """
        if len(self.tac_ops):
            self.tac_ops[-1] = op
        else:
            self.tac_ops.append(op)

    def reset_block_refs(self) -> None:
        """Update all operations and new def sites to refer to this block."""

        for op in self.evm_ops:
            op.block = self
        for op in self.tac_ops:
            op.block = self
            if isinstance(op, TACAssignOp) and isinstance(op.lhs, mem.Variable):
                for site in op.lhs.def_sites:
                    site.block = self

    def build_entry_stack(self) -> bool:
        """
        Construct this block's entry stack by joining all predecessor stacks.

        Returns:
            True iff the new stack is different from the old one.
        """
        old_stack = self.entry_stack
        pred_stacks = [pred.exit_stack for pred in self.preds]
        self.entry_stack = mem.VariableStack.join_all(pred_stacks)
        self.entry_stack.set_max_size(old_stack.max_size)
        self.entry_stack.metafy()

        return old_stack != self.entry_stack

    def build_exit_stack(self) -> bool:
        """
        Apply the transformation in this block's delta stack to construct its
        exit stack from its entry stack.

        Returns:
            True iff a symbolic overflow occurred.
        """
        overflow = False

        # If variables were obtained from deeper than there are extant
        # stack items, the program is possibly popping from an empty stack.
        if settings.die_on_empty_pop \
            and (len(self.entry_stack) < self.delta_stack.empty_pops):
            logging.error("Popped empty stack in %s.", self.ident())
            raise RuntimeError("Popped empty stack in {}.".format(self.ident()))

        # If executing this block would overflow the stack, maybe skip it.
        delta = len(self.delta_stack) - self.delta_stack.empty_pops
        if (len(self.entry_stack) + delta) > self.exit_stack.max_size:
            self.symbolic_overflow = True
            if settings.skip_stack_on_overflow:
                return True
            overflow = True

        # Construct the new exit stack from the entry and delta stacks.
        exit_stack = self.entry_stack.copy()

        # Build a mapping from MetaVariables to the Variables they correspond to.
        metavar_map = {}
        for var in self.delta_stack:
            if isinstance(var, mem.MetaVariable):
                # Here we know the stack is full enough, given we've already checked it,
                # but we'll get a MetaVariable if we try grabbing something off the end.
                metavar_map[var] = exit_stack.peek(var.payload)

        # Construct the exit stack itself.
        exit_stack.pop_many(self.delta_stack.empty_pops)
        for var in list(self.delta_stack)[::-1]:
            if isinstance(var, mem.MetaVariable):
                exit_stack.push(metavar_map[var])
            else:
                exit_stack.push(var)

        self.exit_stack = exit_stack

        return overflow

    def hook_up_stack_vars(self) -> None:
        """
        Replace all stack MetaVariables will be replaced with the actual
        variables they refer to.
        """
        for op in self.tac_ops:
            for i in range(len(op.args)):
                if isinstance(op.args[i], TACArg):
                    stack_var = op.args[i].stack_var
                    if stack_var is not None:
                        # If the required argument is past the end, don't replace the metavariable
                        # as we would thereby lose information.
                        if stack_var.payload < len(self.entry_stack):
                            op.args[i].var = self.entry_stack.peek(stack_var.payload)

    def hook_up_def_site_jumps(self) -> None:
        """
        Add jumps to this block if they can be inferred from its jump variable's
        definition sites.
        """
        if self.last_op.opcode in [opcodes.JUMP, opcodes.JUMPI]:
            dest = self.last_op.args[0].value
            site_vars = [d.get_instruction().lhs for d in dest.def_sites]
            non_top_vars = [v for v in site_vars if not v.is_top]

            existing_dests = [s.entry for s in sorted(self.succs)]

            # join all values to obtain possible jump dests
            # add jumps to those locations if they are valid and don't already exist
            for d in mem.Variable.join_all(non_top_vars):
                if d in existing_dests or not self.cfg.is_valid_jump_dest(d):
                    continue
                for b in self.cfg.get_blocks_by_pc(d):
                    self.cfg.add_edge(self, b)

            self.has_unresolved_jump = (len(non_top_vars) == 0)

    def hook_up_jumps(self) -> bool:
        """
        Connect this block up to any successors that can be inferred
        from this block's jump condition and destination.
        An invalid jump will be replaced with a THROW instruction.

        Returns:
            True iff this block's successor list was modified.
        """
        jumpdests = {}
        # A mapping from a jump dest to all the blocks addressed at that dest

        fallthrough = []
        last_op = self.last_op
        invalid_jump = False
        unresolved = True
        remove_non_fallthrough = False
        remove_fallthrough = False

        if last_op.opcode == opcodes.JUMPI:
            dest = last_op.args[0].value
            cond = last_op.args[1].value

            # If the condition cannot be true, remove the jump.
            if settings.mutate_jumps and cond.is_false:
                self.tac_ops.pop()
                fallthrough = self.cfg.get_blocks_by_pc(last_op.pc + 1)
                unresolved = False
                remove_non_fallthrough = True

            # If the condition must be true, the JUMPI behaves like a JUMP.
            elif settings.mutate_jumps and cond.is_true:
                last_op.opcode = opcodes.JUMP
                last_op.args.pop()

                if self.__handle_valid_dests(dest, jumpdests) and len(jumpdests) == 0:
                    invalid_jump = True

                unresolved = False
                remove_fallthrough = True

            # Otherwise, the condition can't be resolved (it may be either true or false), but check the destination>
            else:
                fallthrough = self.cfg.get_blocks_by_pc(last_op.pc + 1)

                # We've already covered the case that both cond and dest are known,
                # so only handle a variable destination
                if self.__handle_valid_dests(dest, jumpdests) and len(jumpdests) == 0:
                    invalid_jump = True

                if not dest.is_unconstrained:
                    unresolved = False

        elif last_op.opcode == opcodes.JUMP:
            dest = last_op.args[0].value

            if self.__handle_valid_dests(dest, jumpdests) and len(jumpdests) == 0:
                invalid_jump = True

            if not dest.is_unconstrained:
                unresolved = False

        # The final argument is not a JUMP or a JUMPI
        # Note that this case handles THROW and THROWI
        else:
            unresolved = False

            # No terminating jump or a halt; fall through to next block.
            if not last_op.opcode.halts():
                fallthrough = self.cfg.get_blocks_by_pc(self.exit + 1)

        # Block's jump went to an invalid location, replace the jump with a throw
        # Note that a JUMPI could still potentially throw, but not be
        # transformed into a THROWI unless *ALL* its destinations
        # are invalid.
        if settings.generate_throws and invalid_jump:
            self.last_op = TACOp.convert_jump_to_throw(last_op)
        self.has_unresolved_jump = unresolved

        for address, block_list in list(jumpdests.items()):
            to_add = [d for d in block_list if d in self.succs]
            if len(to_add) != 0:
                jumpdests[address] = to_add

        to_add = [d for d in fallthrough if d in self.succs]
        if len(to_add) != 0:
            fallthrough = to_add

        old_succs = list(sorted(self.succs))
        new_succs = {d for dl in list(jumpdests.values()) + [fallthrough] for d in dl}
        if fallthrough:
            self.fallthrough = fallthrough[0]

        for s in old_succs:
            if s not in new_succs and s.entry in jumpdests:
                self.cfg.remove_edge(self, s)

        for s in new_succs:
            if s not in self.succs:
                self.cfg.add_edge(self, s)

        if settings.mutate_jumps:
            fallthrough = self.cfg.get_blocks_by_pc(last_op.pc + 1)
            if remove_non_fallthrough:
                for d in self.succs:
                    if d not in fallthrough:
                        self.cfg.remove_edge(self, d)
            if remove_fallthrough:
                for d in fallthrough:
                    self.cfg.remove_edge(self, d)

        return set(old_succs) != set(self.succs)

    def __handle_valid_dests(self, d: mem.Variable,
                             jumpdests: t.Dict[int, 'TACBasicBlock']):
        """
        Append any valid jump destinations in d to its jumpdest list,
        returning False iff the possible destination set is unconstrained.
        A jump must be considered invalid if it has no valid destinations.
        """
        if d.is_unconstrained:
            return False

        for v in d:
            if self.cfg.is_valid_jump_dest(v):
                jumpdests[v] = [op.block for op in self.cfg.get_ops_by_pc(v)]

        return True

    def apply_operations(self, use_sets=False) -> None:
        """
        Propagate and fold constants through the arithmetic TAC instructions
        in this block.

        If use_sets is True, folding will also be done on Variables that
        possess multiple possible values, performing operations in all possible
        combinations of values.
        """
        for op in self.tac_ops:
            if op.opcode == opcodes.CONST:
                op.lhs.values = op.args[0].value.values
            elif op.opcode.is_arithmetic():
                if op.constant_args() or (op.constrained_args() and use_sets):
                    rhs = [arg.value for arg in op.args]
                    op.lhs.values = mem.Variable.arith_op(op.opcode.name, rhs).values
                elif not op.lhs.is_unconstrained:
                    op.lhs.widen_to_top()


class TACOp(patterns.Visitable):
    """
    A Three-Address Code operation.
    Each operation consists of an opcode object defining its function,
    a list of argument variables, and the unique program counter address
    of the EVM instruction it was derived from.
    """

    def __init__(self, opcode: opcodes.OpCode, args: t.List['TACArg'],
                 pc: int, block=None):
        """
        Args:
          opcode: the operation being performed.
          args: Variables that are operated upon.
          pc: the program counter at the corresponding instruction in the
              original bytecode.
          block: the block this operation belongs to. Defaults to None.
        """
        self.opcode = opcode
        self.args = args
        self.pc = pc
        self.block = block

    def __str__(self):
        if self.opcode in [opcodes.MSTORE, opcodes.MSTORE8, opcodes.SSTORE]:
            if self.opcode == opcodes.MSTORE:
                lhs = "M[{}]".format(self.args[0])
            elif self.opcode == opcodes.MSTORE8:
                lhs = "M8[{}]".format(self.args[0])
            else:
                lhs = "S[{}]".format(self.args[0])

            return "{}: {} = {}".format(hex(self.pc), lhs,
                                        " ".join([str(arg) for arg in self.args[1:]]))
        return "{}: {} {}".format(hex(self.pc), self.opcode,
                                  " ".join([str(arg) for arg in self.args]))

    def __repr__(self):
        return "<{0} object {1}, {2}>".format(
            self.__class__.__name__,
            hex(id(self)),
            self.__str__()
        )

    def constant_args(self) -> bool:
        """True iff each of this operations arguments is a constant value."""
        return all([arg.value.is_const for arg in self.args])

    def constrained_args(self) -> bool:
        """True iff none of this operations arguments is value-unconstrained."""
        return all([not arg.value.is_unconstrained for arg in self.args])

    @classmethod
    def convert_jump_to_throw(cls, op: 'TACOp') -> 'TACOp':
        """
        Given a jump, convert it to a throw, preserving the condition var if JUMPI.
        Otherwise, return the given operation unchanged.
        """
        if op.opcode not in [opcodes.JUMP, opcodes.JUMPI]:
            return op
        elif op.opcode == opcodes.JUMP:
            return cls(opcodes.THROW, [], op.pc, op.block)
        elif op.opcode == opcodes.JUMPI:
            return cls(opcodes.THROWI, [op.args[1]], op.pc, op.block)

    def __deepcopy__(self, memodict={}):
        new_op = type(self)(self.opcode,
                            copy.deepcopy(self.args, memodict),
                            self.pc,
                            self.block)
        return new_op


class TACAssignOp(TACOp):
    """
    A TAC operation that additionally takes a variable to which
    this operation's result is implicitly bound.
    """

    def __init__(self, lhs: mem.Variable, opcode: opcodes.OpCode,
                 args: t.List['TACArg'], pc: int, block=None,
                 print_name: bool = True):
        """
        Args:
          lhs: The Variable that will receive the result of this operation.
          opcode: The operation being performed.
          args: Variables that are operated upon.
          pc: The program counter at this instruction in the original bytecode.
          block: The block this operation belongs to.
          print_name: Some operations (e.g. CONST) don't need to print their
                      name in order to be readable.
        """
        super().__init__(opcode, args, pc, block)
        self.lhs = lhs
        self.print_name = print_name

    def __str__(self):
        if self.opcode in [opcodes.SLOAD, opcodes.MLOAD]:
            if self.opcode == opcodes.SLOAD:
                rhs = "S[{}]".format(self.args[0])
            else:
                rhs = "M[{}]".format(self.args[0])

            return "{}: {} = {}".format(hex(self.pc), self.lhs.identifier, rhs)
        arglist = ([str(self.opcode)] if self.print_name else []) \
                  + [str(arg) for arg in self.args]
        return "{}: {} = {}".format(hex(self.pc), self.lhs.identifier,
                                    " ".join(arglist))

    def __deepcopy__(self, memodict={}):
        """
        Return a copy of this TACAssignOp, deep copying the args and vars,
        but leaving block references unchanged.
        """
        new_op = type(self)(copy.deepcopy(self.lhs, memodict),
                            self.opcode,
                            copy.deepcopy(self.args, memodict),
                            self.pc,
                            self.block,
                            self.print_name)
        return new_op


class TACArg:
    """
    Contains information held in an argument to a TACOp.
    In particular, a TACArg may hold both the current value of an argument,
    if it exists; along with the entry stack position it came from, if it did.
    This allows updated/refined stack data to be propagated into the body
    of a TACBasicBlock.
    """

    def __init__(self, var: mem.Variable = None, stack_var: mem.MetaVariable = None):
        self.var = var
        """The actual variable this arg contains."""
        self.stack_var = stack_var
        """The stack position this variable came from."""

    def __str__(self):
        return str(self.value)

    @property
    def value(self):
        """
        Return this arg's value if it has one, otherwise return its stack variable.
        """

        if self.var is None:
            if self.stack_var is None:
                raise ValueError("TAC Argument has no value.")
            else:
                return self.stack_var
        else:
            return self.var

    @classmethod
    def from_var(cls, var: mem.Variable):
        if isinstance(var, mem.MetaVariable):
            return cls(stack_var=var)
        return cls(var=var)


class TACLocRef:
    """Contains a reference to a program counter within a particular block."""

    def __init__(self, block, pc):
        self.block = block
        """The block that contains the referenced instruction."""
        self.pc = pc
        """The program counter of the referenced instruction."""

    def __deepcopy__(self, memodict={}):
        return type(self)(self.block, self.pc)

    def __str__(self):
        return "{}.{}".format(self.block.ident(), hex(self.pc))

    def __eq__(self, other):
        return self.block == other.block and self.pc == other.pc

    def __hash__(self):
        return hash(self.block) ^ hash(self.pc)

    def get_instruction(self):
        """Return the TACOp referred to by this TACLocRef, if it exists."""
        for i in self.block.tac_ops:
            if i.pc == self.pc:
                return i
        return None


class Destackifier:
    """Converts EVMBasicBlocks into corresponding TACBasicBlocks.

    Most instructions get mapped over directly, except:
        POP: generates no TAC op, but pops the symbolic stack;
        PUSH: generates a CONST TAC assignment operation;
        DUP, SWAP: these simply permute the symbolic stack, generate no ops;
        LOG0 ... LOG4: all translated to a generic LOG instruction

    Additionally, there is a NOP TAC instruction that does nothing, to represent
    a block containing EVM instructions with no corresponding TAC code.
    """

    def __init__(self):
        # A sequence of three-address operations
        self.ops = []

        # The symbolic variable stack we'll be operating on.
        self.stack = mem.VariableStack()

        # Entry address of the current block being converted
        self.block_entry = None

        # The number of TAC variables we've assigned,
        # in order to produce unique identifiers. Typically the same as
        # the number of items pushed to the stack.
        # We increment it so that variable names will be globally unique.
        self.stack_vars = 0

    def __fresh_init(self, evm_block: evm_cfg.EVMBasicBlock) -> None:
        """Reinitialise all structures in preparation for converting a block."""
        self.ops = []
        self.stack = mem.VariableStack()
        self.block_entry = evm_block.evm_ops[0].pc \
            if len(evm_block.evm_ops) > 0 else None

    def __new_var(self) -> mem.Variable:
        """Construct and return a new variable with the next free identifier."""

        # Generate the new variable, numbering it by the implicit stack location
        # it came from.
        var = mem.Variable.top(name="V{}".format(self.stack_vars),
                               def_sites=ssle([TACLocRef(None, self.block_entry)]))
        self.stack_vars += 1
        return var

    def convert_block(self, evm_block: evm_cfg.EVMBasicBlock) -> TACBasicBlock:
        """
        Given a EVMBasicBlock, produce an equivalent three-address code sequence
        and return the resulting TACBasicBlock.
        """
        self.__fresh_init(evm_block)

        for op in evm_block.evm_ops:
            self.__handle_evm_op(op)

        entry = evm_block.evm_ops[0].pc if len(evm_block.evm_ops) > 0 else None
        exit = evm_block.evm_ops[-1].pc + evm_block.evm_ops[-1].opcode.push_len() \
            if len(evm_block.evm_ops) > 0 else None

        # If the block is empty, append a NOP before continuing.
        if len(self.ops) == 0:
            self.ops.append(TACOp(opcodes.NOP, [], entry))

        new_block = TACBasicBlock(entry, exit, self.ops, evm_block.evm_ops,
                                  self.stack)

        # Link up new ops and def sites to the block that contains them.
        new_block.reset_block_refs()

        return new_block

    def __handle_evm_op(self, op: evm_cfg.EVMOp) -> None:
        """
        Produce from an EVM line its corresponding TAC instruction, if there is one,
        appending it to the current TAC sequence, and manipulate the stack in any
        needful way.
        """

        if op.opcode.is_swap():
            self.stack.swap(op.opcode.pop)
        elif op.opcode.is_dup():
            self.stack.dup(op.opcode.pop)
        elif op.opcode == opcodes.POP:
            self.stack.pop()
        else:
            self.__gen_instruction(op)

    def __gen_instruction(self, op: evm_cfg.EVMOp) -> None:
        """
        Given a line, generate its corresponding TAC operation,
        append it to the op sequence, and push any generated
        variables to the stack.
        """

        inst = None
        # All instructions that push anything push exactly
        # one word to the stack. Assign that symbolic variable here.
        new_var = self.__new_var() if op.opcode.push == 1 else None

        # Set this variable's def site
        if new_var is not None:
            for site in new_var.def_sites:
                site.pc = op.pc

        # Generate the appropriate TAC operation.
        # Special cases first, followed by the fallback to generic instructions.
        if op.opcode.is_push():
            args = [TACArg(var=mem.Variable(values=[op.value], name="C"))]
            inst = TACAssignOp(new_var, opcodes.CONST, args, op.pc, print_name=False)
        elif op.opcode.is_missing():
            args = [TACArg(var=mem.Variable(values=[op.value], name="C"))]
            inst = TACOp(op.opcode, args, op.pc)
        elif op.opcode.is_log():
            args = [TACArg.from_var(var) for var in self.stack.pop_many(op.opcode.pop)]
            inst = TACOp(opcodes.LOG, args, op.pc)
        elif op.opcode == opcodes.MLOAD:
            args = [TACArg.from_var(self.stack.pop())]
            inst = TACAssignOp(new_var, op.opcode, args, op.pc)
        elif op.opcode == opcodes.MSTORE:
            args = [TACArg.from_var(var) for var in self.stack.pop_many(opcodes.MSTORE.pop)]
            inst = TACOp(op.opcode, args, op.pc)
        elif op.opcode == opcodes.MSTORE8:
            args = [TACArg.from_var(var) for var in self.stack.pop_many(opcodes.MSTORE8.pop)]
            inst = TACOp(op.opcode, args, op.pc)
        elif op.opcode == opcodes.SLOAD:
            args = [TACArg.from_var(self.stack.pop())]
            inst = TACAssignOp(new_var, op.opcode, args, op.pc)
        elif op.opcode == opcodes.SSTORE:
            args = [TACArg.from_var(var) for var in self.stack.pop_many(opcodes.SSTORE.pop)]
            inst = TACOp(op.opcode, args, op.pc)
        elif new_var is not None:
            args = [TACArg.from_var(var) for var in self.stack.pop_many(op.opcode.pop)]
            inst = TACAssignOp(new_var, op.opcode, args, op.pc)
        else:
            args = [TACArg.from_var(var) for var in self.stack.pop_many(op.opcode.pop)]
            inst = TACOp(op.opcode, args, op.pc)

        # This var must only be pushed after the operation is performed.
        if new_var is not None:
            self.stack.push(new_var)
        self.ops.append(inst)


def getBytecode(path):
    with open(path, 'r') as f:
        return f.read().replace('\n', '')

def getCFG(bytecode):
    graph = TACGraph.from_bytecode(bytecode)
    graph.nx_graph()

    # TODO
    # interesting = ['CALL', 'SSTORE', 'SLOAD', 'DELEGATECALL', 'STATICCALL', 'CALLCODE','SELFDESTRUCT']
    interesting = ['CALL', 'SSTORE', 'DELEGATECALL', 'STATICCALL', 'CALLCODE', 'SELFDESTRUCT', 'TIMESTAMP', 'NUMBER', 'CREATE', 'CREATE2']

    for block in graph.blocks:

        # print('#########################################################')
        #
        # for op in block.evm_ops:
        #    print(op)
        # print(len(block.evm_ops))

        # print(str(block).split('---')[0])
        # print(str(block).split('---')[1])
        # print(str(block).split('---')[2])

        basicBlock = ''
        opcodes = str(block).split('---')[2].split('\n')
        for op in opcodes:
            if op == '':
                continue
            if basicBlock == '':
                basicBlock = basicBlock + str(int(op.split(' ')[0], 16))
            if len(op.split(' ')) == 2:
                opcode = op.split(' ')[1]
            else:
                opcode = op.split(' ')[1] + str(int(op.split(' ')[2], 16))
                #print(opcode)
            if opcode in interesting:
                block.interesting = True
            if 'MISSING' in opcode:
                block.HasMissingOps = True
            basicBlock = basicBlock + opcode

        # print(basicBlock)

        block.block_hash = sha256(basicBlock.encode('utf-8')).hexdigest()
        block.OpcodeCount = len(block.evm_ops)

        # print(str(block))
        # print(block.interesting)
        # print(block.block_hash)
        # print(block.covered)

    # for block in graph.blocks:
    #     print('#########################################################')
    #     print('Block ID: ' + str(hex(block.entry)))
    #     print('Predecessor')
    #     for i in block.preds:
    #         print(i.block_hash)
    #     print('Successor')
    #     for i in block.succs:
    #         print(i.block_hash)

    return graph


def getCFG_test(bytecode):
    graph = TACGraph.from_bytecode(bytecode)

    print(graph.nx_graph())

    # TODO
    # interesting = ['CALL', 'SSTORE', 'SLOAD', 'DELEGATECALL', 'STATICCALL', 'CALLCODE','SELFDESTRUCT']
    interesting = ['CALL', 'SSTORE', 'DELEGATECALL', 'STATICCALL', 'CALLCODE', 'SELFDESTRUCT', 'TIMESTAMP', 'NUMBER', 'CREATE', 'CREATE2']

    for block in graph.blocks:

        print('#########################################################')
        #
        # for op in block.evm_ops:
        #   print(op)

        # print(str(block).split('---')[0])
        # print(str(block).split('---')[1])
        # print(str(block).split('---')[2])

        # for op in block.evm_ops:
        #    print(op)
        # print(len(block.evm_ops))

        basicBlock = ''
        opcodes = str(block).split('---')[2].split('\n')
        for op in opcodes:
            if op == '':
                continue
            if basicBlock == '':
                basicBlock = basicBlock + str(int(op.split(' ')[0], 16))
            if len(op.split(' ')) == 2:
                opcode = op.split(' ')[1]
            else:
                opcode = op.split(' ')[1] + str(int(op.split(' ')[2], 16))
                #print(opcode)
            if opcode in interesting:
                block.interesting = True
            if 'MISSING' in opcode:
                block.HasMissingOps = True
            basicBlock = basicBlock + opcode

        # print(basicBlock)

        block.block_hash = sha256(basicBlock.encode('utf-8')).hexdigest()
        block.OpcodeCount = len(block.evm_ops)

        # if(block.interesting):
        #     print(str(hex(block.entry)))
        print(str(block))

        print(block.block_hash)
        # print(block.covered)

    # for block in graph.blocks:
    #     print('#########################################################')
    #     print('Block ID: ' + str(hex(block.entry)))
    #     print('Predecessor')
    #     for i in block.preds:
    #         print(i.block_hash)
    #     print('Successor')
    #     for i in block.succs:
    #         print(i.block_hash)

    return graph


def MainLoop():
    path_bin = r'./Smart_Contract_Binaries'
    for r, d, f in os.walk(path_bin):
        for file in f:
            if 'CBTokendeployedcode.bin' in file:  # Contract with All successful tx
                bytecode = getBytecode(path_bin + '/' + file)

                graph = TACGraph.from_bytecode(bytecode)

                graph.nx_graph()
                interesting = ['CALL', 'SSTORE', 'SLOAD']

                for block in graph.blocks:

                    # print('#########################################################')
                    # print('Block ID: ' + str(hex(block.entry)))
                    # for op in block.evm_ops:
                    #    print(op)

                    #print(str(block).split('---')[0])
                    #print(str(block).split('---')[1])
                    #print(str(block).split('---')[2])
                    basicBlock = ''
                    opcodes = str(block).split('---')[2].split('\n')
                    for op in opcodes:
                        if op == '':
                            continue
                        if len(op.split(' ')) == 2:
                            opcode = op.split(' ')[1]
                        else:
                            opcode = op.split(' ')[1] + str(int(op.split(' ')[2], 16))
                            # print(opcode)
                        if opcode in interesting:
                            block.interesting = True
                        basicBlock = basicBlock + opcode
                    print(basicBlock)
                    block.block_hash = sha256(basicBlock.encode('utf-8')).hexdigest()
                    #print(str(block))
                    # print(block.interesting)
                    print(block.block_hash)
                    # print(block.covered)


if __name__ == '__main__':
    # MainLoop()
    # getCFG('606060405260006000600050556001600360006101000a81548160ff021916908302179055506000600360016101000a81548160ff02191690830217905550600060046000505560006005600050555b5b610a508061005e6000396000f3606060405236156100b6576000357c01000000000000000000000000000000000000000000000000000000009004806306661abd146101de57806315140bd1146102065780633f948cac1461023057806348cccce9146102585780635aa945a4146102705780636b66ae0e146102d45780636ed65dae14610312578063789d1c5c1461033a57806383a64c1e146103995780639e455939146104195780639eeb30e614610457578063d3e204d714610481576100b6565b6101dc5b600360009054906101000a900460ff16156101bf5760006000818150548092919060010191905055506000600360006101000a81548160ff02191690830217905550600160009054906101000a900473ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff166002600050604051808280546001816001161561010002031660029004801561019f5780601f106101745761010080835404028352916020019161019f565b820191906000526020600020905b81548152906001019060200180831161018257829003601f168201915b50509150506000604051808303816000866161da5a03f1915050506101d9565b6001600360006101000a81548160ff021916908302179055505b5b565b005b34610002576101f06004805050610501565b6040518082815260200191505060405180910390f35b3461000257610218600480505061050a565b60405180821515815260200191505060405180910390f35b3461000257610242600480505061051d565b6040518082815260200191505060405180910390f35b61026e6004808035906020019091905050610526565b005b34610002576102d26004808035906020019091908035906020019082018035906020019191908080601f016020809104026020016040519081016040528093929190818152602001838380828437820191505050505050909091905050610591565b005b34610002576102e66004805050610706565b604051808273ffffffffffffffffffffffffffffffffffffffff16815260200191505060405180910390f35b3461000257610324600480505061072c565b6040518082815260200191505060405180910390f35b6103976004808035906020019091908035906020019082018035906020019191908080601f016020809104026020016040519081016040528093929190818152602001838380828437820191505050505050909091905050610735565b005b34610002576103ab60048050506108b1565b60405180806020018281038252838181518152602001915080519060200190808383829060006004602084601f0104600302600f01f150905090810190601f16801561040b5780820380516001836020036101000a031916815260200191505b509250505060405180910390f35b346100025761042b6004805050610952565b604051808273ffffffffffffffffffffffffffffffffffffffff16815260200191505060405180910390f35b34610002576104696004805050610981565b60405180821515815260200191505060405180910390f35b34610002576104936004805050610994565b60405180806020018281038252838181518152602001915080519060200190808383829060006004602084601f0104600302600f01f150905090810190601f1680156104f35780820380516001836020036101000a031916815260200191505b509250505060405180910390f35b60006000505481565b600360019054906101000a900460ff1681565b60056000505481565b60046000818150548092919060010191905055508073ffffffffffffffffffffffffffffffffffffffff166108fc349081150290604051809050600060405180830381858888f19350505050151561058d5760056000818150548092919060010191905055505b5b50565b6000600360016101000a81548160ff0219169083021790555081600160006101000a81548173ffffffffffffffffffffffffffffffffffffffff021916908302179055508060026000509080519060200190828054600181600116156101000203166002900490600052602060002090601f016020900481019282601f1061062457805160ff1916838001178555610655565b82800160010185558215610655579182015b82811115610654578251826000505591602001919060010190610636565b5b5090506106809190610662565b8082111561067c5760008181506000905550600101610662565b5090565b50508173ffffffffffffffffffffffffffffffffffffffff1681604051808280519060200190808383829060006004602084601f0104600302600f01f150905090810190601f1680156106e75780820380516001836020036101000a031916815260200191505b509150506000604051808303816000866161da5a03f1915050505b5050565b600160009054906101000a900473ffffffffffffffffffffffffffffffffffffffff1681565b60046000505481565b60006001600360016101000a81548160ff0219169083021790555034905082600160006101000a81548173ffffffffffffffffffffffffffffffffffffffff021916908302179055508160026000509080519060200190828054600181600116156101000203166002900490600052602060002090601f016020900481019282601f106107cd57805160ff19168380011785556107fe565b828001600101855582156107fe579182015b828111156107fd5782518260005055916020019190600101906107df565b5b509050610829919061080b565b80821115610825576000818150600090555060010161080b565b5090565b50508273ffffffffffffffffffffffffffffffffffffffff168183604051808280519060200190808383829060006004602084601f0104600302600f01f150905090810190601f1680156108915780820380516001836020036101000a031916815260200191505b5091505060006040518083038185876185025a03f192505050505b505050565b60026000508054600181600116156101000203166002900480601f01602080910402602001604051908101604052809291908181526020018280546001816001161561010002031660029004801561094a5780601f1061091f5761010080835404028352916020019161094a565b820191906000526020600020905b81548152906001019060200180831161092d57829003601f168201915b505050505081565b6000600160009054906101000a900473ffffffffffffffffffffffffffffffffffffffff16905061097e565b90565b600360009054906101000a900460ff1681565b602060405190810160405280600081526020015060026000508054600181600116156101000203166002900480601f016020809104026020016040519081016040528092919081815260200182805460018160011615610100020316600290048015610a415780601f10610a1657610100808354040283529160200191610a41565b820191906000526020600020905b815481529060010190602001808311610a2457829003601f168201915b50505050509050610a4d565b9056')

    # 0xe180b13d2a44e0e82ffb00fad84d453abc108483
    # getCFG_test('0x6080604052600436106101ab5763ffffffff7c0100000000000000000000000000000000000000000000000000000000600035041663015008b18114610259578063018a25e81461027f57806306fdde03146102a65780630f15f4c01461033057806310f01eba1461034557806324c33d33146103665780632660316e146103dd5780632ce219991461040c5780632e19ebdc1461043d5780633ccfd60b146104555780633ddd46981461046a578063438d359e146104c657806349cc635d146104d15780635893d481146104fb578063624ae5c014610516578063630664341461052b578063685ffd8314610561578063747dff42146105b45780638f7140ea146106375780638f8a583214610652578063921dec211461066d57806395d89b41146102a6578063a2bccae9146106c0578063aeeed0db14610701578063c519500e14610715578063c7e284b81461072d578063cd133c8f14610742578063ce89c80c1461074d578063cf80800014610768578063d53b267914610780578063de7874f314610795578063ed78cf4a146107ef578063ee0b5d8b146107f7578063fb9073eb14610850575b6101b36140fc565b60175460009060ff1615156001146101ca57600080fd5b33803b80156101d857600080fd5b600160a060020a03821632146101ed57600080fd5b34633b9aca008110156101ff57600080fd5b69152d02c7e14af680000081111561021657600080fd5b61021f8561086b565b336000908152600e6020908152604080832054808452601090925290912060060154919650945061025290859087610b10565b5050505050005b34801561026557600080fd5b5061027d600160a060020a0360043516602435610d4b565b005b34801561028b57600080fd5b50610294610e65565b60408051918252519081900360200190f35b3480156102b257600080fd5b506102bb610f2b565b6040805160208082528351818301528351919283929083019185019080838360005b838110156102f55781810151838201526020016102dd565b50505050905090810190601f1680156103225780820380516001836020036101000a031916815260200191505b509250505060405180910390f35b34801561033c57600080fd5b5061027d610f62565b34801561035157600080fd5b50610294600160a060020a0360043516611002565b34801561037257600080fd5b5061037e600435611014565b604080519c8d5260208d019b909b528b8b019990995296151560608b015260808a019590955260a089019390935260c088019190915260e087015261010086015261012085015261014084015261016083015251908190036101800190f35b3480156103e957600080fd5b506103f8600435602435611077565b604080519115158252519081900360200190f35b34801561041857600080fd5b50610424600435611097565b6040805192835260208301919091528051918290030190f35b34801561044957600080fd5b506102946004356110b0565b34801561046157600080fd5b5061027d6110c2565b6040805160206004803580820135601f810184900484028501840190955284845261027d94369492936024939284019190819084018382808284375094975050600160a060020a038535169550505050506020013515156113d2565b61027d60043561155b565b3480156104dd57600080fd5b5061027d600435600160a060020a036024351660443560643561166b565b34801561050757600080fd5b506102946004356024356117e2565b34801561052257600080fd5b506102946117ff565b34801561053757600080fd5b50610543600435611805565b60408051938452602084019290925282820152519081900360600190f35b6040805160206004803580820135601f810184900484028501840190955284845261027d9436949293602493928401919081908401838280828437509497505084359550505050506020013515156119ab565b3480156105c057600080fd5b506105c9611a61565b604080519d8e5260208e019c909c528c8c019a909a5260608c019890985260808b019690965260a08a019490945260c0890192909252600160a060020a031660e088015261010087015261012086015261014085015261016084015261018083015251908190036101a00190f35b34801561064357600080fd5b5061027d600435602435611c4f565b34801561065e57600080fd5b5061027d600435602435611cb2565b6040805160206004803580820135601f810184900484028501840190955284845261027d943694929360249392840191908190840183828082843750949750508435955050505050602001351515611d92565b3480156106cc57600080fd5b506106db600435602435611e48565b604080519485526020850193909352838301919091526060830152519081900360800190f35b61027d600160a060020a0360043516611e7a565b34801561072157600080fd5b50610424600435611f94565b34801561073957600080fd5b50610294611fad565b61027d60043561203e565b34801561075957600080fd5b50610294600435602435612131565b34801561077457600080fd5b506102946004356121d8565b34801561078c57600080fd5b506103f861228b565b3480156107a157600080fd5b506107ad600435612294565b60408051600160a060020a0390981688526020880196909652868601949094526060860192909252608085015260a084015260c0830152519081900360e00190f35b61027d6122db565b34801561080357600080fd5b50610818600160a060020a0360043516612358565b604080519788526020880196909652868601949094526060860192909252608085015260a084015260c0830152519081900360e00190f35b34801561085c57600080fd5b5061027d60043560243561242d565b6108736140fc565b336000908152600e60205260408120549080821515610b075760008054604080517fe56556a90000000000000000000000000000000000000000000000000000000081523360048201529051600160a060020a039092169263e56556a9926024808401936020939083900390910190829087803b1580156108f357600080fd5b505af1158015610907573d6000803e3d6000fd5b505050506040513d602081101561091d57600080fd5b505160008054604080517f82e37b2c000000000000000000000000000000000000000000000000000000008152600481018590529051939650600160a060020a03909116926382e37b2c92602480840193602093929083900390910190829087803b15801561098b57600080fd5b505af115801561099f573d6000803e3d6000fd5b505050506040513d60208110156109b557600080fd5b505160008054604080517fe3c08adf000000000000000000000000000000000000000000000000000000008152600481018890529051939550600160a060020a039091169263e3c08adf92602480840193602093929083900390910190829087803b158015610a2357600080fd5b505af1158015610a37573d6000803e3d6000fd5b505050506040513d6020811015610a4d57600080fd5b5051336000818152600e6020908152604080832088905587835260109091529020805473ffffffffffffffffffffffffffffffffffffffff1916909117905590508115610ad6576000828152600f6020908152604080832086905585835260108252808320600190810186905560128352818420868552909252909120805460ff191690911790555b8015801590610ae55750828114155b15610aff5760008381526010602052604090206006018190555b845160010185525b50929392505050565b600d546004805460008381526013602052604090209091015442910181118015610b7c575060008281526013602052604090206002015481111580610b7c575060008281526013602052604090206002015481118015610b7c5750600082815260136020526040902054155b15610b9557610b9082863487600088612531565b610d44565b60008281526013602052604090206002015481118015610bc7575060008281526013602052604090206003015460ff16155b15610d0f576000828152601360205260409020600301805460ff19166001179055610bf18361283a565b925080670de0b6b3a764000002836000015101836000018181525050848360200151018360200181815250507fa7801a70b37e729a11492aad44fd3dba89b4149f0609dc0f6837bf9e57e2671a3360106000888152602001908152602001600020600101543486600001518760200151886040015189606001518a608001518b60a001518c60c001518d60e00151604051808c600160a060020a0316600160a060020a031681526020018b600019166000191681526020018a815260200189815260200188815260200187600160a060020a0316600160a060020a0316815260200186600019166000191681526020018581526020018481526020018381526020018281526020019b50505050505050505050505060405180910390a15b600085815260106020526040902060030154610d31903463ffffffff612c5316565b6000868152601060205260409020600301555b5050505050565b610d536140fc565b601754600090819060ff161515600114610d6c57600080fd5b33803b8015610d7a57600080fd5b600160a060020a0382163214610d8f57600080fd5b85633b9aca00811015610da157600080fd5b69152d02c7e14af6800000811115610db857600080fd5b336000908152600e60205260409020549450600160a060020a0388161580610de85750600160a060020a03881633145b15610e06576000858152601060205260409020600601549350610e4f565b600160a060020a0388166000908152600e60209081526040808320548884526010909252909120600601549094508414610e4f5760008581526010602052604090206006018490555b610e5b85858989612ccb565b5050505050505050565b600d546004805460008381526013602052604081209092015491929142910181118015610ed4575060008281526013602052604090206002015481111580610ed4575060008281526013602052604090206002015481118015610ed45750600082815260136020526040902054155b15610f1c57600082815260136020526040902060050154610f1590670de0b6b3a764000090610f09908263ffffffff612c5316565b9063ffffffff612ef016565b9250610f26565b6544364c5bb00092505b505090565b60408051808201909152600681527f504f4f484d4f0000000000000000000000000000000000000000000000000000602082015281565b600154600160a060020a03163314610f7957600080fd5b60175460ff1615610f8957600080fd5b6017805460ff19166001908117909155600d819055600454600354600092909252601360205242808301919091037f4155c2f711f2cdd34f8262ab8fb9b7020a700fe7b6948222152f7670d1fdf3515560055401017f4155c2f711f2cdd34f8262ab8fb9b7020a700fe7b6948222152f7670d1fdf34f55565b600e6020526000908152604090205481565b601360205260009081526040902080546001820154600283015460038401546004850154600586015460068701546007880154600889015460098a0154600a8b0154600b909b0154999a9899979860ff909716979596949593949293919290918c565b601260209081526000928352604080842090915290825290205460ff1681565b6015602052600090815260409020805460019091015482565b600f6020526000908152604090205481565b6000806000806110d06140fc565b60175460ff1615156001146110e457600080fd5b33803b80156110f257600080fd5b600160a060020a038216321461110757600080fd5b600d54336000908152600e6020908152604080832054848452601390925290912060020154919850429750955086118015611154575060008781526013602052604090206003015460ff16155b801561116d575060008781526013602052604090205415155b15611313576000878152601360205260409020600301805460ff191660011790556111978361283a565b92506111a285612f1d565b935060008411156111f357600085815260106020526040808220549051600160a060020a039091169186156108fc02918791818181858888f193505050501580156111f1573d6000803e3d6000fd5b505b85670de0b6b3a764000002836000015101836000018181525050848360200151018360200181815250507f0bd0dba8ab932212fa78150cdb7b0275da72e255875967b5cad11464cf71bedc3360106000888152602001908152602001600020600101548686600001518760200151886040015189606001518a608001518b60a001518c60c001518d60e00151604051808c600160a060020a0316600160a060020a031681526020018b600019166000191681526020018a815260200189815260200188815260200187600160a060020a0316600160a060020a0316815260200186600019166000191681526020018581526020018481526020018381526020018281526020019b50505050505050505050505060405180910390a16113c9565b61131c85612f1d565b9350600084111561136d57600085815260106020526040808220549051600160a060020a039091169186156108fc02918791818181858888f1935050505015801561136b573d6000803e3d6000fd5b505b6000858152601060209081526040918290206001015482513381529182015280820186905260608101889052905186917f8f36579a548bc439baa172a6521207464154da77f411e2da3db2f53affe6cc3a919081900360800190a25b50505050505050565b6000808080808033803b80156113e757600080fd5b600160a060020a03821632146113fc57600080fd5b6114058b612fb0565b600054604080517faa4d490b000000000000000000000000000000000000000000000000000000008152336004820181905260248201859052600160a060020a038f811660448401528e151560648401528351959d50909b50349a509092169263aa4d490b928a92608480830193919282900301818588803b15801561148a57600080fd5b505af115801561149e573d6000803e3d6000fd5b50505050506040513d60408110156114b557600080fd5b508051602091820151600160a060020a03808b166000818152600e865260408082205485835260108852918190208054600190910154825188151581529889018790529416878201526060870193909352608086018c90524260a0870152915193995091975095508a92909186917fdd6176433ff5026bbce96b068584b7bbe3514227e72df9c630b749ae87e64442919081900360c00190a45050505050505050505050565b6115636140fc565b601754600090819060ff16151560011461157c57600080fd5b33803b801561158a57600080fd5b600160a060020a038216321461159f57600080fd5b34633b9aca008110156115b157600080fd5b69152d02c7e14af68000008111156115c857600080fd5b6115d18661086b565b336000908152600e60205260409020549096509450861580611603575060008581526010602052604090206001015487145b15611621576000858152601060205260409020600601549350611660565b6000878152600f602090815260408083205488845260109092529091206006015490945084146116605760008581526010602052604090206006018490555b6113c9858588610b10565b600054600160a060020a0316331461168257600080fd5b600160a060020a0383166000908152600e602052604090205484146116bd57600160a060020a0383166000908152600e602052604090208490555b6000828152600f602052604090205484146116e4576000828152600f602052604090208490555b600084815260106020526040902054600160a060020a0384811691161461173a576000848152601060205260409020805473ffffffffffffffffffffffffffffffffffffffff1916600160a060020a0385161790555b60008481526010602052604090206001015482146117675760008481526010602052604090206001018290555b60008481526010602052604090206006015481146117945760008481526010602052604090206006018190555b600084815260126020908152604080832085845290915290205460ff1615156117dc5760008481526012602090815260408083208584529091529020805460ff191660011790555b50505050565b601460209081526000928352604080842090915290825290205481565b600d5481565b600d546000818152601360205260408120600201549091829182919042118015611841575060008181526013602052604090206003015460ff16155b801561185a575060008181526013602052604090205415155b1561197b5760008181526013602052604090205485141561193f576000818152601360205260409020600701546118c89060649061189f90603063ffffffff61351e16565b8115156118a857fe5b60008881526010602052604090206002015491900463ffffffff612c5316565b600086815260116020908152604080832085845290915290206002015461192190611903906118f789866135ac565b9063ffffffff61366e16565b6000888152601060205260409020600301549063ffffffff612c5316565b600087815260106020526040902060040154919550935091506119a3565b60008581526010602090815260408083206002908101546011845282852086865290935292209091015461192190611903906118f789866135ac565b60008581526010602052604090206002810154600590910154611921906119039088906136e5565b509193909250565b6000808080808033803b80156119c057600080fd5b600160a060020a03821632146119d557600080fd5b6119de8b612fb0565b600054604080517f745ea0c1000000000000000000000000000000000000000000000000000000008152336004820181905260248201859052604482018f90528d151560648301528251949c509a50349950600160a060020a039092169263745ea0c1928a92608480830193919282900301818588803b15801561148a57600080fd5b600080600080600080600080600080600080600080600d54905060136000828152602001908152602001600020600901548160136000848152602001908152602001600020600501546013600085815260200190815260200160002060020154601360008681526020019081526020016000206004015460136000878152602001908152602001600020600701546013600088815260200190815260200160002060000154600a0260136000898152602001908152602001600020600101540160106000601360008b815260200190815260200160002060000154815260200190815260200160002060000160009054906101000a9004600160a060020a031660106000601360008c815260200190815260200160002060000154815260200190815260200160002060010154601460008b8152602001908152602001600020600080815260200190815260200160002054601460008c815260200190815260200160002060006001815260200190815260200160002054601460008d815260200190815260200160002060006002815260200190815260200160002054601460008e8152602001908152602001600020600060038152602001908152602001600020549d509d509d509d509d509d509d509d509d509d509d509d509d5050909192939495969798999a9b9c565b600054600160a060020a03163314611c6657600080fd5b600082815260126020908152604080832084845290915290205460ff161515611cae5760008281526012602090815260408083208484529091529020805460ff191660011790555b5050565b611cba6140fc565b60175460009060ff161515600114611cd157600080fd5b33803b8015611cdf57600080fd5b600160a060020a0382163214611cf457600080fd5b84633b9aca00811015611d0657600080fd5b69152d02c7e14af6800000811115611d1d57600080fd5b336000908152600e60205260409020549350861580611d3b57508387145b15611d59576000848152601060205260409020600601549650611d86565b6000848152601060205260409020600601548714611d865760008481526010602052604090206006018790555b6113c984888888612ccb565b6000808080808033803b8015611da757600080fd5b600160a060020a0382163214611dbc57600080fd5b611dc58b612fb0565b600054604080517fc0942dfd000000000000000000000000000000000000000000000000000000008152336004820181905260248201859052604482018f90528d151560648301528251949c509a50349950600160a060020a039092169263c0942dfd928a92608480830193919282900301818588803b15801561148a57600080fd5b601160209081526000928352604080842090915290825290208054600182015460028301546003909301549192909184565b611e826140fc565b601754600090819060ff161515600114611e9b57600080fd5b33803b8015611ea957600080fd5b600160a060020a0382163214611ebe57600080fd5b34633b9aca00811015611ed057600080fd5b69152d02c7e14af6800000811115611ee757600080fd5b611ef08661086b565b336000908152600e60205260409020549096509450600160a060020a0387161580611f235750600160a060020a03871633145b15611f41576000858152601060205260409020600601549350611660565b600160a060020a0387166000908152600e602090815260408083205488845260109092529091206006015490945084146116605760008581526010602052604090206006018490556113c9858588610b10565b6016602052600090815260409020805460019091015482565b600d54600081815260136020526040812060020154909190429081101561203557600480546000848152601360205260409020909101540181111561200e57600082815260136020526040902060020154610f15908263ffffffff61366e16565b60048054600084815260136020526040902090910154610f1591018263ffffffff61366e16565b60009250610f26565b6120466140fc565b60175460009060ff16151560011461205d57600080fd5b33803b801561206b57600080fd5b600160a060020a038216321461208057600080fd5b34633b9aca0081101561209257600080fd5b69152d02c7e14af68000008111156120a957600080fd5b6120b28561086b565b336000908152600e602052604090205490955093508515806120d357508386145b156120f157600084815260106020526040902060060154955061211e565b600084815260106020526040902060060154861461211e5760008481526010602052604090206006018690555b612129848787610b10565b505050505050565b600480546000848152601360205260408120909201544291018111801561219a57506000848152601360205260409020600201548111158061219a57506000848152601360205260409020600201548111801561219a5750600084815260136020526040902054155b156121c8576000848152601360205260409020600601546121c1908463ffffffff61374216565b91506121d1565b6121c183613763565b5092915050565b600d5460048054600083815260136020526040812090920154919291429101811180156122475750600082815260136020526040902060020154811115806122475750600082815260136020526040902060020154811180156122475750600082815260136020526040902054155b1561227b57600082815260136020526040902060050154612274908590610f09908263ffffffff612c5316565b9250612284565b612274846137db565b5050919050565b60175460ff1681565b6010602052600090815260409020805460018201546002830154600384015460048501546005860154600690960154600160a060020a039095169593949293919290919087565b600d54600101600081815260136020526040902060070154612303903463ffffffff612c5316565b600082815260136020908152604091829020600701929092558051838152349281019290925280517f74b1d2f771e0eff1b2c36c38499febdbea80fe4013bdace4fc4b653322c2895c9281900390910190a150565b6000806000806000806000806000600d54915050600160a060020a0389166000908152600e60209081526040808320548084526010808452828520600180820154601187528588208989528752948720015495839052935260028301546005909301549093849390916123ee906123d09086906136e5565b6000878152601060205260409020600301549063ffffffff612c5316565b600095865260106020908152604080882060040154601183528189209989529890915290952054939e929d50909b509950919750919550909350915050565b6124356140fc565b601754600090819060ff16151560011461244e57600080fd5b33803b801561245c57600080fd5b600160a060020a038216321461247157600080fd5b85633b9aca0081101561248357600080fd5b69152d02c7e14af680000081111561249a57600080fd5b336000908152600e602052604090205494508715806124c9575060008581526010602052604090206001015488145b156124e7576000858152601060205260409020600601549350610e4f565b6000888152600f60209081526040808320548884526010909252909120600601549094508414610e4f576000858152601060205260409020600601849055610e5b85858989612ccb565b6000858152601160209081526040808320898452909152812060010154819081901515612565576125628885613848565b93505b60008981526013602052604090206006015468056bc75e2d631000001180156125bf575060008881526011602090815260408083208c8452909152902054674563918244f40000906125bd908963ffffffff612c5316565b115b156126465760008881526011602090815260408083208c84529091529020546125f790674563918244f400009063ffffffff61366e16565b9250612609878463ffffffff61366e16565b60008981526010602052604090206003015490925061262e908363ffffffff612c5316565b60008981526010602052604090206003015591955085915b633b9aca0087111561282f57600089815260136020526040902060060154612674908863ffffffff61374216565b9050670de0b6b3a764000081106126eb5761268f818a6138a8565b60008981526013602052604090205488146126b65760008981526013602052604090208890555b60008981526013602052604090206001015485146126e35760008981526013602052604090206001018590555b835160640184525b60008881526011602090815260408083208c845290915290206001015461271990829063ffffffff612c5316565b60008981526011602090815260408083208d84529091529020600181019190915554612746908890612c53565b60008981526011602090815260408083208d845282528083209390935560139052206005015461277d90829063ffffffff612c5316565b60008a81526013602052604090206005810191909155600601546127a890889063ffffffff612c5316565b60008a81526013602090815260408083206006019390935560148152828220828052905220546127df90889063ffffffff612c5316565b60008a815260146020908152604080832083805290915281209190915561280e908a908a908a908a9089613986565b935061281f89898960008589613b85565b935061282f886000898488613cd5565b505050505050505050565b6128426140fc565b600d546000818152601360205260408120805460018201546007909201549092808080808080606461287b89603063ffffffff61351e16565b81151561288457fe5b04965060328860008b81526016602052604090205491900496506064906128b2908a9063ffffffff61351e16565b8115156128bb57fe5b60008b81526016602052604090206001015491900495506064906128e6908a9063ffffffff61351e16565b8115156128ef57fe5b04935061290a846118f787818a818e8e63ffffffff61366e16565b60008c81526013602052604090206005015490935061293786670de0b6b3a764000063ffffffff61351e16565b81151561294057fe5b60008d815260136020526040902060050154919004925061298e90670de0b6b3a76400009061297690859063ffffffff61351e16565b81151561297f57fe5b8791900463ffffffff61366e16565b905060008111156129be576129a9858263ffffffff61366e16565b94506129bb838263ffffffff612c5316565b92505b60008a8152601060205260409020600201546129e190889063ffffffff612c5316565b60008b815260106020526040808220600201929092556001549151600160a060020a039092169188156108fc0291899190818181858888f19350505050158015612a2f573d6000803e3d6000fd5b5060028054600160a060020a0316906108fc90612a5f90612a53886003810461366e565b9063ffffffff61351e16565b6040518115909202916000818181858888f19350505050158015612a87573d6000803e3d6000fd5b50612a958860038604612c53565b60008c8152601360205260409020600781019190915560080154612ac090839063ffffffff612c5316565b601360008d815260200190815260200160002060080181905550601360008c815260200190815260200160002060020154620f4240028d60000151018d60000181815250508867016345785d8a0000028a6a52b7d2dcc80cd2e4000000028e6020015101018d6020018181525050601060008b815260200190815260200160002060000160009054906101000a9004600160a060020a03168d60400190600160a060020a03169081600160a060020a031681525050601060008b8152602001908152602001600020600101548d606001906000191690816000191681525050868d6080018181525050848d60e0018181525050838d60c0018181525050828d60a0018181525050600d600081548092919060010191905055508a806001019b505042601360008d815260200190815260200160002060040181905550612c226007612c09613e39565b60068110612c1357fe5b0154429063ffffffff612c5316565b60008c8152601360205260409020600281018290556007018490556006558c9b505050505050505050505050919050565b81810182811015612cc557604080517f08c379a000000000000000000000000000000000000000000000000000000000815260206004820152601360248201527f536166654d61746820616464206661696c656400000000000000000000000000604482015290519081900360640190fd5b92915050565b600d546004805460008381526013602052604090209091015442910181118015612d37575060008281526013602052604090206002015481111580612d37575060008281526013602052604090206002015481118015612d375750600082815260136020526040902054155b15612d7757612d49846118f788612f1d565b6010600088815260200190815260200160002060030181905550612d7282878688600088612531565b612129565b60008281526013602052604090206002015481118015612da9575060008281526013602052604090206003015460ff16155b15612129576000828152601360205260409020600301805460ff19166001179055612dd38361283a565b925080670de0b6b3a764000002836000015101836000018181525050858360200151018360200181815250507f88261ac70d02d5ea73e54fa6da17043c974de1021109573ec1f6f57111c823dd336010600089815260200190815260200160002060010154856000015186602001518760400151886060015189608001518a60a001518b60c001518c60e00151604051808b600160a060020a0316600160a060020a031681526020018a6000191660001916815260200189815260200188815260200187600160a060020a0316600160a060020a0316815260200186600019166000191681526020018581526020018481526020018381526020018281526020019a505050505050505050505060405180910390a1505050505050565b6000612f16612f0d612f08858563ffffffff61366e16565b6137db565b6118f7856137db565b9392505050565b6000818152601060205260408120600501548190612f3c908490613ecd565b600083815260106020526040902060048101546003820154600290920154612f7a92612f6e919063ffffffff612c5316565b9063ffffffff612c5316565b90506000811115612fa65760008381526010602052604081206002810182905560038101829055600401555b8091505b50919050565b8051600090829082808060208411801590612fcb5750600084115b1515612fd657600080fd5b846000815181101515612fe557fe5b90602001015160f860020a900460f860020a02600160f860020a031916602060f860020a021415801561304c5750846001850381518110151561302457fe5b90602001015160f860020a900460f860020a02600160f860020a031916602060f860020a0214155b151561305757600080fd5b84600081518110151561306657fe5b90602001015160f860020a900460f860020a02600160f860020a031916603060f860020a021415613113578460018151811015156130a057fe5b90602001015160f860020a900460f860020a02600160f860020a031916607860f860020a02141515156130d257600080fd5b8460018151811015156130e157fe5b90602001015160f860020a900460f860020a02600160f860020a031916605860f860020a021415151561311357600080fd5b600091505b838210156135015784517f40000000000000000000000000000000000000000000000000000000000000009086908490811061315057fe5b90602001015160f860020a900460f860020a02600160f860020a0319161180156131c4575084517f5b00000000000000000000000000000000000000000000000000000000000000908690849081106131a557fe5b90602001015160f860020a900460f860020a02600160f860020a031916105b156132315784828151811015156131d757fe5b90602001015160f860020a900460f860020a0260f860020a900460200160f860020a02858381518110151561320857fe5b906020010190600160f860020a031916908160001a90535082151561322c57600192505b6134f6565b848281518110151561323f57fe5b90602001015160f860020a900460f860020a02600160f860020a031916602060f860020a02148061330f575084517f60000000000000000000000000000000000000000000000000000000000000009086908490811061329b57fe5b90602001015160f860020a900460f860020a02600160f860020a03191611801561330f575084517f7b00000000000000000000000000000000000000000000000000000000000000908690849081106132f057fe5b90602001015160f860020a900460f860020a02600160f860020a031916105b806133b9575084517f2f000000000000000000000000000000000000000000000000000000000000009086908490811061334557fe5b90602001015160f860020a900460f860020a02600160f860020a0319161180156133b9575084517f3a000000000000000000000000000000000000000000000000000000000000009086908490811061339a57fe5b90602001015160f860020a900460f860020a02600160f860020a031916105b15156133c457600080fd5b84828151811015156133d257fe5b90602001015160f860020a900460f860020a02600160f860020a031916602060f860020a02141561344057848260010181518110151561340e57fe5b90602001015160f860020a900460f860020a02600160f860020a031916602060f860020a021415151561344057600080fd5b821580156134ec575084517f30000000000000000000000000000000000000000000000000000000000000009086908490811061347957fe5b90602001015160f860020a900460f860020a02600160f860020a03191610806134ec575084517f3900000000000000000000000000000000000000000000000000000000000000908690849081106134cd57fe5b90602001015160f860020a900460f860020a02600160f860020a031916115b156134f657600192505b600190910190613118565b60018315151461351057600080fd5b505050506020015192915050565b600082151561352f57506000612cc5565b5081810281838281151561353f57fe5b0414612cc557604080517f08c379a000000000000000000000000000000000000000000000000000000000815260206004820152601360248201527f536166654d617468206d756c206661696c656400000000000000000000000000604482015290519081900360640190fd5b600082815260116020908152604080832084845282528083206001908101546013808552838620600581015493810154875260168652938620548787529452600790920154670de0b6b3a76400009361365d9392612a5392909161363491879160649161361e9163ffffffff61351e16565b81151561362757fe5b049063ffffffff61351e16565b81151561363d57fe5b60008881526013602052604090206008015491900463ffffffff612c5316565b81151561366657fe5b049392505050565b6000828211156136df57604080517f08c379a000000000000000000000000000000000000000000000000000000000815260206004820152601360248201527f536166654d61746820737562206661696c656400000000000000000000000000604482015290519081900360640190fd5b50900390565b600082815260116020908152604080832084845282528083206002810154600190910154601390935290832060080154612f1692670de0b6b3a76400009161372c9161351e565b81151561373557fe5b049063ffffffff61366e16565b6000612f1661375084613763565b6118f7613763868663ffffffff612c5316565b60006309502f906137cb6d03b2a1d15167e7c5699bfde000006118f76137c67a0dac7055469777a6122ee4310dd6c14410500f2904840000000000612f6e6b01027e72f1f1281308800000612a538a670de0b6b3a764000063ffffffff61351e16565b613f64565b8115156137d457fe5b0492915050565b60006137ee670de0b6b3a7640000613fb7565b6137cb600261382161380e86670de0b6b3a764000063ffffffff61351e16565b65886c8f6730709063ffffffff61351e16565b81151561382a57fe5b04612f6e61383786613fb7565b6304a817c89063ffffffff61351e16565b6138506140fc565b6000838152601060205260409020600501541561388457600083815260106020526040902060050154613884908490613ecd565b50600d546000838152601060205260409020600501558051600a0181528092915050565b600081815260136020526040812060020154429190821180156138d75750600083815260136020526040902054155b156138fb576138f482612f6e600a670de0b6b3a764000088613627565b9050613928565b60008381526013602052604090206002015461392590612f6e600a670de0b6b3a764000088613627565b90505b60065461393b908363ffffffff612c5316565b81101561395b5760008381526013602052604090206002018190556117dc565b60065461396e908363ffffffff612c5316565b60008481526013602052604090206002015550505050565b61398e6140fc565b6000808080606489600154604051929091049550600160a060020a0316908590600081818185875af19250505015156139c75760009392505b600a890491508988141580156139ed575060008881526010602052604090206001015415155b15613a8d57600088815260106020526040902060040154613a1590839063ffffffff612c5316565b600089815260106020908152604091829020600481019390935582546001909301548251600160a060020a03909416845290830152818101849052426060830152518b918d918b917f590bbc0fc16915a85269a48f74783c39842b7ae9eceb7c295c95dbe8b3ec7331919081900360800190a4613a91565b8192505b600087815260156020526040902060010154613ad390606490613abb908c9063ffffffff61351e16565b811515613ac457fe5b8591900463ffffffff612c5316565b92506000831115613b7657506002805490830490600160a060020a03166108fc613afd858461366e565b6040518115909202916000818181858888f19350505050158015613b25573d6000803e3d6000fd5b5060008b815260136020526040902060070154613b48908263ffffffff612c5316565b60008c81526013602052604090206007015560c0860151613b7090849063ffffffff612c5316565b60c08701525b50939998505050505050505050565b613b8d6140fc565b60008481526015602052604081205481908190606490613bb4908a9063ffffffff61351e16565b811515613bbd57fe5b049250613c31613c246064613bf1601560008c8152602001908152602001600020600101548c61351e90919063ffffffff16565b811515613bfa57fe5b046064613c0e8c600e63ffffffff61351e16565b811515613c1757fe5b049063ffffffff612c5316565b899063ffffffff61366e16565b9750613c43888463ffffffff61366e16565b9150613c518a8a8589613fc3565b90506000811115613c6f57613c6c838263ffffffff61366e16565b92505b60008a815260136020526040902060070154613c9590612f6e848463ffffffff612c5316565b60008b81526013602052604090206007015560e0850151613cbd90849063ffffffff612c5316565b60e08601525061010084015250909695505050505050565b836c01431e0fae6d7217caa00000000242670de0b6b3a76400000282600001510101816000018181525050600d54751aba4714957d300d0e549208b31adb100000000000000285826020015101018160200181815250507f3671a735b2c7f1e43f1ab4385d4c5b480bbff437ad893b703fb0dfdbd24679e28160000151826020015160106000898152602001908152602001600020600101543387878760400151886060015189608001518a60a001518b60c001518c60e001518d6101000151604051808e81526020018d81526020018c600019166000191681526020018b600160a060020a0316600160a060020a031681526020018a815260200189815260200188600160a060020a0316600160a060020a0316815260200187600019166000191681526020018681526020018581526020018481526020018381526020018281526020019d505050505050505050505050505060405180910390a15050505050565b604080516000194301406020808301919091528251808303820181529183019283905281516000938493600693909282918401908083835b60208310613e905780518252601f199092019160209182019101613e71565b5181516020939093036101000a6000190180199091169216919091179052604051920182900390912092505050811515613ec657fe5b0692915050565b6000613ed983836136e5565b90506000811115613f5f57600083815260106020526040902060030154613f0790829063ffffffff612c5316565b6000848152601060209081526040808320600301939093556011815282822085835290522060020154613f4190829063ffffffff612c5316565b60008481526011602090815260408083208684529091529020600201555b505050565b6000806002613f74846001612c53565b811515613f7d57fe5b0490508291505b81811015612faa578091506002613fa68285811515613f9f57fe5b0483612c53565b811515613faf57fe5b049050613f84565b6000612cc5828361351e565b60008481526013602052604081206005015481908190613ff186670de0b6b3a764000063ffffffff61351e16565b811515613ffa57fe5b600089815260136020526040902060080154919004925061402290839063ffffffff612c5316565b600088815260136020526040902060080155670de0b6b3a764000061404d838663ffffffff61351e16565b81151561405657fe5b60008881526011602090815260408083208c84528252808320600201546013909252909120600801549290910492506140a991612f6e908490670de0b6b3a76400009061372c908a63ffffffff61351e16565b60008781526011602090815260408083208b84528252808320600201939093556013905220600501546140f190670de0b6b3a76400009061297690859063ffffffff61351e16565b979650505050505050565b6101206040519081016040528060008152602001600081526020016000600160a060020a0316815260200160008019168152602001600081526020016000815260200160008152602001600081526020016000815250905600a165627a7a723058206fcd47907c370ed34bcb2f8dbb717ada59d6968f1f4f5f5bf08b38fe465a89160029')
    getCFG_test('0x608060405260043610603e5763ffffffff7c01000000000000000000000000000000000000000000000000000000006000350416633ccfd60b81146046575b60446058565b005b348015605157600080fd5b5060446086565b30313411156084576001805473ffffffffffffffffffffffffffffffffffffffff191633179055426000555b565b60015473ffffffffffffffffffffffffffffffffffffffff16331460a957600080fd5b60005461465001421160ba57600080fd5b6040513390303180156108fc02916000818181858888f1935050505015801560e6573d6000803e3d6000fd5b505600a165627a7a72305820ecf5ce6335323d657ae93678b06b5cd7473824ab7561b8bb77b0b81043f6f4250029')