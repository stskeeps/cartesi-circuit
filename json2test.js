const fs = require("fs");
const process = require("process");

const steps = JSON.parse(fs.readFileSync(process.argv[2])).steps;

for (var i = 0; i < steps.length; i++) {
    var access_paddr = Array(16).fill(0);
    var access_val = Array(16).fill(0);
    var access_readWriteEnd = Array(16).fill(0);
    var ram_page = Array(8192/8).fill("0x0");
    var ram_page_read = Array(8192/8).fill(0);
    
    for (var j = 0; j < steps[i].accesses.length; j++) {
        access_paddr[j] = steps[i].accesses[j].address;
        access_readWriteEnd[j] = steps[i].accesses[j].type == "read" ? 0 : 1;
        access_val[j] = "0x" + Buffer.from(steps[i].accesses[j].value, "hex").readBigUInt64LE(0).toString(16);
        let paddr = steps[i].accesses[j].address;
        if (access_readWriteEnd[j] == 0) {
             if (paddr < 1024) {
                if (ram_page_read[paddr / 8] == 0) {
                   ram_page_read[paddr / 8] = 1;
                   ram_page[paddr / 8] = access_val[j];
                }
             } else {
               let off = paddr - 0x70000000 + 1024;
               if (ram_page_read[off / 8] == 0) {
                  ram_page_read[off / 8] = 1;
                  ram_page[off / 8] = access_val[j];
               }
             }
        }
    }
    if (ram_page_read.length > 8192/8) {
           console.log("too long");
           process.exit(1);
    }
    if (ram_page.length > 8192/8) {
           console.log("too long");
           process.exit(1);
    }
    var ram_page_after = [...ram_page];
    for (var j = 0; j < steps[i].accesses.length; j++) {
        let paddr = steps[i].accesses[j].address;
        if (access_readWriteEnd[j] == 1) {
             if (paddr < 1024) {
                   ram_page_after[paddr / 8] = access_val[j];
             } else {
               let off = paddr - 0x70000000 + 1024;
               ram_page_after[off / 8] = access_val[j];
             }
        }
    }
    
    access_readWriteEnd[steps[i].accesses.length] = 2;
    console.log('input := { ram: ' + JSON.stringify(ram_page).replaceAll('"', '') + '; ram_disagree: ' + JSON.stringify(ram_page_after).replaceAll('"', '') + '; access_paddr: ' + JSON.stringify(access_paddr) + '; access_val: ' + JSON.stringify(access_val).replaceAll('"', '') +'; access_readWriteEnd: ' + JSON.stringify(access_readWriteEnd) + '; };');
    console.log('return_value == 0;');
    console.log('---');
}