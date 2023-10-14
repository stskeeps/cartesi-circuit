
~/HyCC/bin/cbmc-gc --minimization-time-limit 60 --bool mpc_main reference.c

~/HyCC/bin/circuit-utils mpc_main.circ --as-bristol bristol_circuit.txt

