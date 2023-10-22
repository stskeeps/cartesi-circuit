const fs = require("fs");
const process = require("process");

const steps = JSON.parse(fs.readFileSync(process.argv[2])).steps;

var stepsOut = Array(steps.length).fill({});

for (var i = 0; i < steps.length; i++) {
    stepsOut[i] = {}   
    stepsOut[i].access_paddr = Array(16).fill(0);
    stepsOut[i].access_val = Array(16).fill(0);
    stepsOut[i].access_readWriteEnd = Array(16).fill(0);
    
    var ram_page_orig = Buffer.from(steps[i].circuit_ram, "hex");
    if (ram_page_orig.length != 8192) {
        throw "bad " + ram_page_orig.length;
    }
    stepsOut[i].ram = Array(1024).fill(0);
    for (var j = 0; j < 1024; j++) {
        stepsOut[i].ram[j] = "0x" + ram_page_orig.readBigUint64LE(j*8).toString(16);
    }
    if (i > 0) {
//        console.log(JSON.stringify(stepsOut[i-1].ram_after));
//        console.log(JSON.stringify(stepsOut[i].ram));
        for (var j = 0; j < 1024; j++) {
           if (stepsOut[i-1].ram_after[j] !== stepsOut[i].ram[j]) {
               console.log("access log mismatch " + j);
           }
        }
    }
    for (var j = 0; j < steps[i].accesses.length; j++) {
        stepsOut[i].access_paddr[j] = steps[i].accesses[j].address;
        stepsOut[i].access_readWriteEnd[j] = steps[i].accesses[j].type == "read" ? 0 : 1;
        stepsOut[i].access_val[j] = "0x" + Buffer.from(steps[i].accesses[j].value, "hex").readBigUInt64LE(0).toString(16);
    }
    if (stepsOut[i].ram.length > 8192/8) {
           console.log("too long");
           process.exit(1);
    }

    var ram_page_after_orig = Buffer.from(steps[i].circuit_ram, "hex");
    if (ram_page_after_orig.length != 8192) {
        throw "bad " + ram_page_after_orig.length;
    }
    stepsOut[i].ram_after = Array(1024).fill(0);
    for (var j = 0; j < 1024; j++) {
        stepsOut[i].ram_after[j] = "0x" + ram_page_after_orig.readBigUint64LE(j*8).toString(16);
    }
    
    for (var j = 0; j < steps[i].accesses.length; j++) {
        let paddr = stepsOut[i].access_paddr[j];
        if (stepsOut[i].access_readWriteEnd[j] == 1) {
             if (paddr < 1024) {
                   stepsOut[i].ram_after[paddr / 8] = stepsOut[i].access_val[j];
             } else {
               let off = paddr - 0x70000000 + 1024;
               if (off / 8 > 1024) {
                   throw "out of range write 0x" + paddr.toString("hex");
               }
               stepsOut[i].ram_page_after[off / 8] = stepsOut[i].access_val[j];
             }
        }
    }
    stepsOut[i].access_readWriteEnd[steps[i].accesses.length] = 2;
//    console.log("after: " + JSON.stringify(stepsOut[i].ram_after));
/*    console.log('input := { ram: ' + JSON.stringify(ram_page).replaceAll('"', '') + '; ram_disagree: ' + JSON.stringify(ram_page_after).replaceAll('"', '') + '; access_paddr: ' + JSON.stringify(access_paddr) + '; access_val: ' + JSON.stringify(access_val).replaceAll('"', '') +'; access_readWriteEnd: ' + JSON.stringify(access_readWriteEnd) + '; };');
    console.log('return_value == 0;');
    console.log('---'); */
}

//console.log("consistency check");

for (let step = 0; step < stepsOut.length; step++) {
    if (step > 0) {
        for (var j = 0; j < 1024; j++) {
           if (stepsOut[step-1].ram_after[j] !== stepsOut[step].ram[j]) {
               console.log("access log mismatch " + j +  " " + stepsOut[step-1].ram_after[j] + " " +  stepsOut[step].ram[j]);
           }
        } 
    }
}
//console.log("consistency check done");

const MAX_CYCLE = 1024*1024*1024;
const BISECTION_STEPS = 30;

const disagreeStep = 11;

	let left = 0;
	let right = MAX_CYCLE;
	let lastAgree = 0;
	let lastDisagree = MAX_CYCLE;

	let prover_bisection_cycle = Array(BISECTION_STEPS).fill(0);
        let verifier_bisections = Array(BISECTION_STEPS).fill(0);
        

    prover_bisection_RAM = Array(BISECTION_STEPS).fill([]);
     let bisect_step = 0;
     
     for (let i = 0; i < BISECTION_STEPS; i++) {
		let mid = Math.floor((left + right) / 2);
//                console.log("Bisect step " + i + " mid " + mid);

		prover_bisection_cycle[i] = mid;
		if (mid >= stepsOut.length) {
//		   console.log("Got out of range step " + mid + " >= " + stepsOut.length + ", repeating last step, assuming halted state");
		   prover_bisection_RAM[i] = stepsOut[stepsOut.length - 1].ram_after;
		} else {
//		   console.log("setting ram for " + (bisect_step) + " for " + mid);
                   prover_bisection_RAM[i] = stepsOut[mid].ram;
                }
		if (mid < disagreeStep) {
			lastAgree = mid;
			left = mid + 1;
			verifier_bisections[i] = 1;
		} else {
			lastDisagree = mid;
			right = mid - 1;
			verifier_bisections[i] = 0;
		}
		bisect_step++;
	}  
	let agree_ram = 0, disagree_ram = 0;
	for (let i = 0; i < BISECTION_STEPS; i++) {
		if (prover_bisection_cycle[i] == lastAgree) {
			agree_ram = i;
		}
	}
	for (let i = 0; i < BISECTION_STEPS; i++) {
		if (prover_bisection_cycle[i] == lastDisagree) {
        		disagree_ram = i;
		}
	}
/*

console.log("agree_ram: " + agree_ram);
console.log("disagree_ram: " + disagree_ram);
*/

prover_agree_RAM = stepsOut[lastAgree].ram;
prover_disagree_RAM = stepsOut[lastAgree + 1].ram;

if (lastAgree + 1 != lastDisagree) {
  throw "weird";
}
/*
console.log("last agree: " + lastAgree);
console.log("last disagree " +lastDisagree);
console.log("verifier bisections: " + verifier_bisections);

console.log(JSON.stringify(stepsOut[lastAgree].ram_after));
console.log(JSON.stringify(stepsOut[lastAgree+1].ram));

for (let i = 0; i < 1024; i++) {
    if (stepsOut[lastAgree].ram_after[i] !== stepsOut[lastAgree + 1].ram[i]) {
       console.log("inconsitency, " + i + " " + stepsOut[lastAgree].ram_after[i] + " " + stepsOut[lastAgree + 1].ram[i]);
    }
}
*/

/* console.log(JSON.stringify(prover_bisection_RAM));
*/

if (prover_agree_RAM.length != 1024 || prover_disagree_RAM.length != 1024) {
   console.log("ram mismatch");
   process.exit(1);
}

if (prover_bisection_RAM.length != 30) {
   console.log("bisection RAM mismatch");
   process.exit(1);
}
if (verifier_bisections.length != 30) {
   console.log("bisections mismatch");
   process.exit(1);
}

console.log('input := { ram: ' + JSON.stringify(stepsOut[lastAgree].ram).replaceAll('"', '') + '; ram_disagree: ' + JSON.stringify(stepsOut[lastAgree+1].ram).replaceAll('"', '') + '; ' + 
    'prover_bisection_RAM: ' + JSON.stringify(prover_bisection_RAM).replaceAll('"', '') + '; ' +
    /* lastAgree isn't perfect here for > steps.length */
    'access_paddr: ' + JSON.stringify(stepsOut[lastAgree].access_paddr) + '; access_val: ' + JSON.stringify(stepsOut[lastAgree].access_val).replaceAll('"', '') +'; access_readWriteEnd: ' + JSON.stringify(stepsOut[lastAgree].access_readWriteEnd) + '; ' + 
    'verifier_bisections: ' + JSON.stringify(verifier_bisections) + '; pad: 0; };');
console.log('return_value == 0;');
console.log('---');

let tester = '#define RV64I_VERBOSE\n#define __CPROVER_assume(x) do { } while (0)\n#include <stdio.h>\n#include "rv64i.c"\n'
tester += 'int main() {\n';
tester += '  // ' + lastAgree + ' and ' + lastDisagree + '\n';
tester += '  struct BisectInput input = {\n';
tester += '     .ram = ' + JSON.stringify(stepsOut[lastAgree].ram).replaceAll('"', '').replaceAll("[", "{").replaceAll("]", "}") + ',\n';
tester += '     .ram_disagree = ' + JSON.stringify(stepsOut[lastAgree+1].ram).replaceAll('"', '').replaceAll("[", "{").replaceAll("]", "}") + ',\n';
tester += '     .prover_bisection_RAM = ' + JSON.stringify(prover_bisection_RAM).replaceAll('"', '').replaceAll("[", "{").replaceAll("]", "}") + ',\n';
tester += '     .access_paddr = ' + JSON.stringify(stepsOut[lastAgree].access_paddr).replaceAll("[", "{").replaceAll("]", "}") + ',\n';
tester += '     .access_val = ' + JSON.stringify(stepsOut[lastAgree].access_val).replaceAll('"', '').replaceAll("[", "{").replaceAll("]", "}") + ',\n';
tester += '     .access_readWriteEnd = ' + JSON.stringify(stepsOut[lastAgree].access_readWriteEnd).replaceAll("[", "{").replaceAll("]", "}") + ',\n';
tester += '     .verifier_bisections = ' + JSON.stringify(verifier_bisections).replaceAll("[", "{").replaceAll("]", "}") + ', .pad = 0 };\n';
tester += '   return mpc_main(input); }\n';

fs.writeFileSync("tester.c", tester);
