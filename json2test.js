const fs = require("fs");
const process = require("process");

const steps = JSON.parse(fs.readFileSync(process.argv[2])).steps;

const siblingsLength = 61;
for (var p = 0; p < steps.length; p++) {
    let buf = Buffer.alloc(0);
    let rawAccesses = steps[p].accesses;
    let arrayLen = rawAccesses.length;
    
    for (let i = 0; i < arrayLen; i++) {
        if (rawAccesses[i].type == "read") {
            buf = Buffer.concat([buf, Buffer.from(rawAccesses[i].value, "hex")]);
        }
        buf = Buffer.concat([buf, Buffer.from(rawAccesses[i].proof.target_hash, "hex")]);
        for (
              let j = i * (siblingsLength + 1) + 1;
              j < (i + 1) * (siblingsLength + 1);
              j++
            ) {
            buf = Buffer.concat([buf, Buffer.from(rawAccesses[i].proof.sibling_hashes[
                                siblingsLength - (j % (siblingsLength + 1))], "hex")]);
        }
        let finalBuf = Buffer.alloc(20480);
        buf.copy(finalBuf);
        let rootHash = Buffer.from(rawAccesses[i].proof.root_hash, "hex");
        
        console.log('input := { rootHash: ' + JSON.stringify(Array.from(rootHash)) + '; accessLog: ' + JSON.stringify(Array.from(finalBuf)) + '; };');
        console.log('return_value == 0;');
        console.log('---');
    } /*
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
    console.log('---');*/
}