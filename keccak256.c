#include "keccak256.h"

struct MiniRV32IMAState
{
        uint8_t memory[8192];
        uint8_t digest[32];
};

int mpc_main(struct MiniRV32IMAState state) {
        uint8_t hash[32];

        for (int i = 0; i < 32; i++) {
            hash[i] = 0;
        }
        // do hashing here:
        Keccak_SHA256(state.memory, 8192, hash);
        int ret = 0;
        for (int i = 0; i < 32; i++) {
                if (state.digest[i] != hash[i]) {
                    ret = 1;
                }
        }
        return ret;
}
