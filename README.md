
time ~/HyCC/bin/cbmc-gc rv64i.c --minimization-time-limit 120 --bool rv64i --bool sanityCheck --bool run_step --bool mpc_main --merge
~/HyCC/bin/circuit-utils mpc_main.circ --as-bristol bristol_circuit.txt


--

test circuit:

( for x in *.spec; do ../bin/circuit-sim mpc_main.circ --spec-file $x; done ) | tee log

