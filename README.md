
~/HyCC/bin/cbmc-gc --minimization-time-limit 60 --bool mpc_main rv64i.c

~/HyCC/bin/circuit-utils mpc_main.circ --as-bristol bristol_circuit.txt


--

test circuit:

( for x in *.spec; do ../bin/circuit-sim mpc_main.circ --spec-file $x; done ) | tee log
