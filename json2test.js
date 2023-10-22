const fs = require("fs");
const process = require("process");

const steps = JSON.parse(fs.readFileSync(process.argv[2])).steps;

var stepsOut = Array(steps.length).fill({});

for (var i = 0; i < steps.length; i++) {
   
    stepsOut[i].access_paddr = Array(16).fill(0);
    stepsOut[i].access_val = Array(16).fill(0);
    stepsOut[i].access_readWriteEnd = Array(16).fill(0);
    
    var ram_page_orig = Buffer.from(steps[i].circuit_ram, "hex");
    stepsOut[i].ram = Array(1024).fill(0);
    for (var j = 0; j < 1024; j++) {
        stepsOut[i].ram[j] = "0x" + ram_page_orig.readBigUint64LE(j*8).toString(16);
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

    var ram_page_after = [...stepsOut[i].ram];
    for (var j = 0; j < steps[i].accesses.length; j++) {
        let paddr = steps[i].accesses[j].address;
        if (stepsOut[i].access_readWriteEnd[j] == 1) {
             if (paddr < 1024) {
                   ram_page_after[paddr / 8] = stepsOut[i].access_val[j];
             } else {
               let off = paddr - 0x70000000 + 1024;
               ram_page_after[off / 8] = stepsOut[i].access_val[j];
             }
        }
    }
    stepsOut[i].ram_after = ram_page_after;
    stepsOut[i].access_readWriteEnd[steps[i].accesses.length] = 2;
/*    console.log('input := { ram: ' + JSON.stringify(ram_page).replaceAll('"', '') + '; ram_disagree: ' + JSON.stringify(ram_page_after).replaceAll('"', '') + '; access_paddr: ' + JSON.stringify(access_paddr) + '; access_val: ' + JSON.stringify(access_val).replaceAll('"', '') +'; access_readWriteEnd: ' + JSON.stringify(access_readWriteEnd) + '; };');
    console.log('return_value == 0;');
    console.log('---'); */
}

const MAX_CYCLE = 1024*1024*1024;
const BISECTION_STEPS = 30;

const disagreeStep = 4;

	let left = 0;
	let right = MAX_CYCLE;
	let lastAgree = 0;
	let lastDisagree = MAX_CYCLE;

	let prover_bisection_cycle = Array(BISECTION_STEPS + 1).fill(0);
        let verifier_bisections = Array(BISECTION_STEPS).fill(0);
        

prover_bisection_RAM = Array(BISECTION_STEPS + 1).fill([]);
prover_bisection_RAM[0] = stepsOut[0].ram;

     let bisect_step = 0;
     
     for (let i = 0; i < BISECTION_STEPS; i++) {
		let mid = Math.floor((left + right) / 2);
  //              console.log("Bisect step " + i + " mid " + mid);

		prover_bisection_cycle[bisect_step + 1] = mid;
		if (mid >= stepsOut.length) {
//		   console.log("Got out of range step " + mid + " >= " + stepsOut.length + ", repeating last step, assuming halted state");
		   prover_bisection_RAM[bisect_step + 1] = stepsOut[stepsOut.length - 1].ram_after;
		} else {
                   prover_bisection_RAM[bisect_step + 1] = stepsOut[mid].ram;
                }
		if (mid < disagreeStep) {
			lastAgree = mid;
			left = mid + 1;
			verifier_bisections[bisect_step] = 1;
		} else {
			lastDisagree = mid;
			right = mid - 1;
			verifier_bisections[bisect_step] = 0;
		}
		bisect_step++;
	}  
	let agree_ram = 0, disagree_ram = 0;
	for (let i = 0; i < BISECTION_STEPS + 1; i++) {
		if (prover_bisection_cycle[i] == lastAgree) {
			agree_ram = i;
		}
	}
	for (let i = 0; i < BISECTION_STEPS + 1; i++) {
		if (prover_bisection_cycle[i] == lastDisagree) {
        		disagree_ram = i;
		}
	}

prover_agree_RAM = prover_bisection_RAM[agree_ram];
prover_disagree_RAM = prover_bisection_RAM[disagree_ram];

/* console.log("last agree: " + lastAgree);
console.log("last disagree " +lastDisagree);
console.log("verifier bisections: " + verifier_bisections);

console.log(JSON.stringify(prover_bisection_RAM));
*/

console.log('input := { ram: ' + JSON.stringify(prover_agree_RAM).replaceAll('"', '') + '; ram_disagree: ' + JSON.stringify(prover_disagree_RAM).replaceAll('"', '') + '; ' + 
    'prover_bisection_RAM: ' + JSON.stringify(prover_bisection_RAM).replaceAll('"', '') + '; ' +
    /* lastAgree isn't perfect here for > steps.length */
    'access_paddr: ' + JSON.stringify(stepsOut[lastAgree].access_paddr) + '; access_val: ' + JSON.stringify(stepsOut[lastAgree].access_val).replaceAll('"', '') +'; access_readWriteEnd: ' + JSON.stringify(stepsOut[lastAgree].access_readWriteEnd) + '; ' + 
    'verifier_bisections: ' + JSON.stringify(verifier_bisections) + ' };');
console.log('return_value == 0;');
console.log('---');