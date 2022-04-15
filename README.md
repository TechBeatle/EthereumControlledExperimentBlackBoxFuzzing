# The Effects of Blockchain Environment on Security Vulnerability Detection in Fuzzing Ethereum Smart Contracts: An Empirical Study

In this work, we report the first empirical study the effects of the Blockchain environment on fuzz testing of Ethereum Smart Contracts.

The study has two parts:

(i) Part One is a controlled experiment on blackbox fuzzing to study the effects of three design factors. 

(a) Sender Addressing
(b) Execution Order
(c) Resource Allocation

(ii) Part Two is a case study to explore the applicability of the result of Part One to greybox fuzzing.

 
# Controlled Experiment
The Controlled Experiment is implemented in the file "BB_Fuzzer.py"
 
# Case Study
The Case Study is impplemented in the file "AFL_Blockchain.py"
 
 
# Setup

We performed the controlled experiment and the case study in a sandbox equipped with 64GB RAM and an 8-core Intel Xeon 2.2 GHz processor running Ubuntu 18.04 with GETH 1.9.0 as the Ethereum protocol in the EVM for interaction with the Ethereum blockchain installed.

Before starting the experiment on a linux equipped machine, move the 'geth' file to directory usr/bin/ and install golang to avoid any problems.
