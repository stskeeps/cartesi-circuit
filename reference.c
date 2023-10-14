#include <inttypes.h>


	#define MINIRV32_STORE4( ofs, val ) *(uint32_t*)(state.memory + ofs) = val
	#define MINIRV32_STORE2( ofs, val ) *(uint16_t*)(state.memory + ofs) = val
	#define MINIRV32_STORE1( ofs, val ) *(uint8_t*)(state.memory + ofs) = val
	#define MINIRV32_LOAD4( ofs ) *(uint32_t*)(state.memory + ofs)
	#define MINIRV32_LOAD2( ofs ) *(uint16_t*)(state.memory + ofs)
	#define MINIRV32_LOAD1( ofs ) *(uint8_t*)(state.memory + ofs)
	#define MINIRV32_LOAD2_SIGNED( ofs ) *(int16_t*)(state.memory + ofs)
	#define MINIRV32_LOAD1_SIGNED( ofs ) *(int8_t*)(state.memory + ofs)

#define CSR( x ) state.x
#define SETCSR( x, val ) { state.x = val; }
#define REG( x ) state.regs[x]
#define REGSET( x, val ) { state.regs[x] = val; }

#define MINI_RV32_RAM_SIZE 1024
#define MINIRV32_RAM_IMAGE_OFFSET 0x100
struct MiniRV32IMAState
{
	uint32_t regs[32];

	uint32_t pc;
		
	uint8_t merkle[32][16];
	uint8_t memory[1024];
	uint8_t icount;
};


uint32_t mpc_main(struct MiniRV32IMAState state)
{
	int32_t pc = CSR( pc );
	uint32_t rval = 0;
	uint32_t trap = 0;

	//for (state.icount = 0; state.icount < 1; state.icount++) {
		uint32_t ir = 0;
		rval = 0;
		uint32_t ofs_pc = pc - MINIRV32_RAM_IMAGE_OFFSET;
	
		if( ofs_pc >= MINI_RV32_RAM_SIZE )
		{
			trap = 1 + 1;  // Handle access violation on instruction read.
			return trap;
		}
		else if( ofs_pc & 3 )
		{
			trap = 1 + 0;  //Handle PC-misaligned access
			return trap;
		}
		else
		{
			ir = MINIRV32_LOAD4( ofs_pc );
			uint32_t rdid = (ir >> 7) & 0x1f;
			switch( ir & 0x7f )
			{
				case 0x37: // LUI (0b0110111)
					rval = ( ir & 0xfffff000 );
					break;
				case 0x17: // AUIPC (0b0010111)
					rval = pc + ( ir & 0xfffff000 );
					break;
				case 0x6F: // JAL (0b1101111)
				{
					int32_t reladdy = ((ir & 0x80000000)>>11) | ((ir & 0x7fe00000)>>20) | ((ir & 0x00100000)>>9) | ((ir&0x000ff000));
					if( reladdy & 0x00100000 ) reladdy |= 0xffe00000; // Sign extension.
					rval = pc + 4;
					pc = pc + reladdy - 4;
					break;
				}
				case 0x67: // JALR (0b1100111)
				{
					uint32_t imm = ir >> 20;
					int32_t imm_se = imm | (( imm & 0x800 )?0xfffff000:0);
					rval = pc + 4;
					pc = ( (REG( (ir >> 15) & 0x1f ) + imm_se) & ~1) - 4;
					break;
				}
				case 0x63: // Branch (0b1100011)
				{
					uint32_t immm4 = ((ir & 0xf00)>>7) | ((ir & 0x7e000000)>>20) | ((ir & 0x80) << 4) | ((ir >> 31)<<12);
					if( immm4 & 0x1000 ) immm4 |= 0xffffe000;
					int32_t rs1 = REG((ir >> 15) & 0x1f);
					int32_t rs2 = REG((ir >> 20) & 0x1f);
					immm4 = pc + immm4 - 4;
					rdid = 0;
					switch( ( ir >> 12 ) & 0x7 )
					{
						// BEQ, BNE, BLT, BGE, BLTU, BGEU
						case 0: if( rs1 == rs2 ) pc = immm4; break;
						case 1: if( rs1 != rs2 ) pc = immm4; break;
						case 4: if( rs1 < rs2 ) pc = immm4; break;
						case 5: if( rs1 >= rs2 ) pc = immm4; break; //BGE
						case 6: if( (uint32_t)rs1 < (uint32_t)rs2 ) pc = immm4; break;   //BLTU
						case 7: if( (uint32_t)rs1 >= (uint32_t)rs2 ) pc = immm4; break;  //BGEU
						default: trap = (2+1);
					}
					break;
				}
				case 0x03: // Load (0b0000011)
				{
					uint32_t rs1 = REG((ir >> 15) & 0x1f);
					uint32_t imm = ir >> 20;
					int32_t imm_se = imm | (( imm & 0x800 )?0xfffff000:0);
					uint32_t rsval = rs1 + imm_se;

					rsval -= MINIRV32_RAM_IMAGE_OFFSET;
					if( rsval >= MINI_RV32_RAM_SIZE-3 )
					{
					    trap = (5+1);
					    rval = rsval;
					}
					else
					{
						switch( ( ir >> 12 ) & 0x7 )
						{
							//LB, LH, LW, LBU, LHU
							case 0: rval = MINIRV32_LOAD1_SIGNED( rsval ); break;
							case 1: rval = MINIRV32_LOAD2_SIGNED( rsval ); break;
							case 2: rval = MINIRV32_LOAD4( rsval ); break;
							case 4: rval = MINIRV32_LOAD1( rsval ); break;
							case 5: rval = MINIRV32_LOAD2( rsval ); break;
							default: trap = (2+1);
						}
					}
					break;
				}
				case 0x23: // Store 0b0100011
				{
					uint32_t rs1 = REG((ir >> 15) & 0x1f);
					uint32_t rs2 = REG((ir >> 20) & 0x1f);
					uint32_t addy = ( ( ir >> 7 ) & 0x1f ) | ( ( ir & 0xfe000000 ) >> 20 );
					if( addy & 0x800 ) addy |= 0xfffff000;
					addy += rs1 - MINIRV32_RAM_IMAGE_OFFSET;
					rdid = 0;

					if( addy >= MINI_RV32_RAM_SIZE-3 )
					{
						trap = (7+1); // Store access fault.
						rval = addy;
					}
					else
					{
						switch( ( ir >> 12 ) & 0x7 )
						{
							//SB, SH, SW
							case 0: MINIRV32_STORE1( addy, rs2 ); break;
							case 1: MINIRV32_STORE2( addy, rs2 ); break;
							case 2: MINIRV32_STORE4( addy, rs2 ); break;
							default: trap = (2+1);
						}
					}
					break;
				}
				case 0x13: // Op-immediate 0b0010011
				case 0x33: // Op           0b0110011
				{
					uint32_t imm = ir >> 20;
					imm = imm | (( imm & 0x800 )?0xfffff000:0);
					uint32_t rs1 = REG((ir >> 15) & 0x1f);
					uint32_t is_reg = !!( ir & 0x20 );
					uint32_t rs2 = is_reg ? REG(imm & 0x1f) : imm;

					if( is_reg && ( ir & 0x02000000 ) )
					{
                                                trap = (2+1);
					}
					else
					{
						switch( (ir>>12)&7 ) // These could be either op-immediate or op commands.  Be careful.
						{
							case 0: rval = (is_reg && (ir & 0x40000000) ) ? ( rs1 - rs2 ) : ( rs1 + rs2 ); break; 
							case 1: rval = rs1 << (rs2 & 0x1F); break;
							case 2: rval = (int32_t)rs1 < (int32_t)rs2; break;
							case 3: rval = rs1 < rs2; break;
							case 4: rval = rs1 ^ rs2; break;
							case 5: rval = (ir & 0x40000000 ) ? ( ((int32_t)rs1) >> (rs2 & 0x1F) ) : ( rs1 >> (rs2 & 0x1F) ); break;
							case 6: rval = rs1 | rs2; break;
							case 7: rval = rs1 & rs2; break;
						}
					}
					break;
				}
				case 0x0f: // 0b0001111
					rdid = 0;   // fencetype = (ir >> 12) & 0b111; We ignore fences in this impl.
					break;
				default: trap = (2+1); // Fault: Invalid opcode.
			}
			// If there was a trap, do NOT allow register writeback.
			if( trap )
				return trap;

			if( rdid )
			{
				REGSET( rdid, rval ); // Write back register.
			}
		}
		if( trap )
		{
			return trap;
		}
		SETCSR( pc, pc );
//	}
	return 0;
}

