const fs = require("fs");
const process = require("process");

const steps = JSON.parse(fs.readFileSync(process.argv[2])).steps;

for (var i = 0; i < steps.length; i++) {
    var access_paddr = Array(16).fill(0);
    var access_val = Array(16).fill(0);
    var access_readWriteEnd = Array(16).fill(0);
    for (var j = 0; j < steps[i].accesses.length; j++) {
        access_paddr[j] = steps[i].accesses[j].address;
        access_readWriteEnd[j] = steps[i].accesses[j].type == "read" ? 0 : 1;
        access_val[j] = "0x" + Buffer.from(steps[i].accesses[j].value, "hex").readBigUInt64LE(0).toString(16);
    }
    access_readWriteEnd[steps[i].accesses.length] = 2;
    console.log('input := { access_paddr: ' + JSON.stringify(access_paddr) + '; access_val: ' + JSON.stringify(access_val).replaceAll('"', '') +'; access_readWriteEnd: ' + JSON.stringify(access_readWriteEnd) + '; };');
    console.log('return_value == 0;');
    console.log('---');
}