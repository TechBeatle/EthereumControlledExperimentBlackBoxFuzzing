#!/bin/bash
geth  --identity "TestNode2" --rpc -rpcaddr "0.0.0.0"  --rpcport "8545" --rpccorsdomain "*" --port "30303" --nodiscover  --rpcapi "db,eth,net,web3,miner,net,personal,net,txpool,debug,admin"  --networkid 1900    --datadir \Ethereum --allow-insecure-unlock --nat "any" --ipcdisable --nousb --miner.gastarget '900000000000' --dev --dev.period 1
