/*
 ============================================================================
 Name        : MIPSsim.c
 Author      : Kishore Rajasekar
 Version     : v1.2 (Main memory implementation)
 Copyright   : Copyright (C) Kishore Rajasekar - All Rights Reserved
               Unauthorized copying of this file, via any medium is strictly 
               prohibited.
               Proprietary and confidential.
 Description : PIpelined MIPS simulator. Can hold upto 100 each of instructions and data
 ============================================================================
 */
/* On my honor, I have neither given nor received unauthorized aid on this 
assignment */

#include <stdio.h>
#include <string.h> //for char* strcpy(char*,char*)

#define MEMORY_SIZE 100
#define CAT_MASK 0xE0000000
#define CAT1_OPCODE_MASK 0x1C000000
#define CAT2N3_OPCODE_MASK 0x00070000
#define IMME_MASK 0x0000FFFF
#define RS_MASK 0x1F000000
#define RT_MASK 0x00F80000
#define RD_MASK 0x0000F800
#define CAT1_RT_MASK 0x001F0000
#define CAT1_BASE_MASK 0x03E00000
#define CAT1_RT_OFFSET 16
#define CAT1_BASE_OFFSET 21
#define CAT_OFFSET 28
#define CAT1_OPCODE_OFFSET 26
#define CAT2N3_OPCODE_OFFSET 16
#define RS_OFFSET 24
#define RT_OFFSET 19
#define RD_OFFSET 11
#define PRG_ADD_OFFSET 128
#define OPCODE_ERROR -99
#define INSTR_USED -5

static int InstrMem[MEMORY_SIZE];
static int DataMem[MEMORY_SIZE];
static char InstrStr[MEMORY_SIZE][32];
static int instrLength;
static int dataLength;

static int regSet[32] = {0};
static unsigned int PC;
static int data_start_address;

static int preIssue[4]= {-1,-1,-1,-1};
static int waitInstr = -1;
static int execInstr = -1;
static int preALU[2]= {-1,-1};
static int preMem[3] = {-1};//0 - instr, 1- destination reg, 2 - result/source/mem dest
static int postMem[3] = {-1};//0 - instr, 1- destination reg, 2 - result/source/mem dest
static int postALU[3] = {-1};//0 - instr, 1- destination reg, 2 - result

static int FPpreIssue[4]= {-1,-1,-1,-1};
static int FPpreALU[2]= {-1,-1};
static int FPpreMem[3] = {-1};//0 - instr, 1- destination reg, 2 - result/source/mem dest
static int FPpostMem[3] = {-1};//0 - instr, 1- destination reg, 2 - result/source/mem dest
static int FPpostALU[3] = {-1};//0 - instr, 1- destination reg, 2 - result

static unsigned int regInUse = 0;

int fetch(void){
	int preIssueFull = 0;
	int instrCount;
	unsigned int instr;
	int isBreak = 0;
	int catValue;
	int opcode;
	int rs,rt,imm_val=0;
	
	if (preIssue[2] == -1)
		preIssueFull = 2;
	else if (preIssue[3] == -1)
		preIssueFull = 1;
	else
		return 0;//preIssue full
	//copy current queue values into floating pin set
	FPpreIssue[0] = preIssue[0];FPpreIssue[1] = preIssue[1];FPpreIssue[2] = preIssue[2];FPpreIssue[3] = preIssue[3];//FPpreIssue[4] = preIssue[4];FPpreIssue[5] = preIssue[5];
	//reset executed instr counter
	execInstr = -1;
	if (waitInstr != -1){ // there is a pending branch instr, fetch stalled
		instr = InstrMem[waitInstr];
		opcode = (instr & CAT1_OPCODE_MASK)>>CAT1_OPCODE_OFFSET;
		switch (opcode){
			case 0x2: //BEQ instruction
				rs = (instr & CAT1_BASE_MASK)>>CAT1_BASE_OFFSET;
				rt = (instr & CAT1_RT_MASK)>>CAT1_RT_OFFSET;
				if (((regInUse & (1 << rs)) == 0) && ((regInUse & (1 << rt)) == 0)){
					imm_val = (instr & IMME_MASK)<<2;// following convention, to optimize, <<2 and /4 in the end cancel each other out :P
					if(regSet[rs]==regSet[rt]){
						if((imm_val & 0x00020000) == 1) imm_val = -1*(((imm_val^0xFFFFFFFF)&0x0003FFFF)+1);
						PC+=imm_val/4;
					}
					execInstr = waitInstr;
					waitInstr = -1;
				}
				break;
			case 0x4: //BGTZ instruction
				rs = (instr & CAT1_BASE_MASK)>>CAT1_BASE_OFFSET;
				if ((regInUse & (1 << rs)) == 0){
					imm_val = (instr & IMME_MASK)<<2;
					if(regSet[rs] > 0){
						if((imm_val & 0x00020000) == 1) imm_val = -1*(((imm_val^0xFFFFFFFF)&0x0003FFFF)+1);
						PC+=imm_val/4;
					}
					execInstr = waitInstr;
					waitInstr = -1;
				}
				break;
			default:
				//I shouldnt be here
				break;
		}
		return isBreak;
	}
	while(preIssueFull != 0){
		instrCount = PC++;
		if(instrCount > instrLength || instrCount < 0){printf("Program terminated. Reason:Suspicious behaviour observed, attempt to access program code beyond its own scope");return 1;}
		instr = InstrMem[instrCount];
		catValue = (instr & CAT_MASK)>>CAT_OFFSET;
		switch (catValue){
			case 0x0: // Category 1
				opcode = (instr & CAT1_OPCODE_MASK)>>CAT1_OPCODE_OFFSET;
				switch (opcode){
					case 0x0: //J instruction
						imm_val = (instr & 0x03FFFFFF)<<2;//should add first 4 bits from PC, but absolutely not necessary for the small scenario that is to be tested. :P
						PC = (imm_val - PRG_ADD_OFFSET)/4;
						execInstr = instrCount;
						return isBreak;
						break;
					case 0x2: //BEQ instruction
						rs = (instr & CAT1_BASE_MASK)>>CAT1_BASE_OFFSET;
						rt = (instr & CAT1_RT_MASK)>>CAT1_RT_OFFSET;
						if (((regInUse & (1 << rs)) == 0) && ((regInUse & (1 << rt)) == 0)){
							imm_val = (instr & IMME_MASK)<<2;// following convention, to optimize, <<2 and /4 in the end cancel each other out :P
							if(regSet[rs]==regSet[rt]){
								if((imm_val & 0x00020000) == 1) imm_val = -1*(((imm_val^0xFFFFFFFF)&0x0003FFFF)+1);
								PC+=imm_val/4;
							}
							execInstr = instrCount;
						}
						else
							waitInstr = instrCount;
						return isBreak;
						break;
					case 0x4: //BGTZ instruction
						rs = (instr & CAT1_BASE_MASK)>>CAT1_BASE_OFFSET;
						if ((regInUse & (1 << rs)) == 0){
							imm_val = (instr & IMME_MASK)<<2;
							if(regSet[rs] > 0){
								if((imm_val & 0x00020000) == 1) imm_val = -1*(((imm_val^0xFFFFFFFF)&0x0003FFFF)+1);
								PC+=imm_val/4;
							}
							execInstr = instrCount;
						}
						else
							waitInstr = instrCount;
						return isBreak;	
						break;
					case 0x5: //BREAK instruction
						isBreak = 1;
						execInstr = instrCount;
						return isBreak;
						break;
					case 0x6: //SW instruction
					case 0x7: //LW instruction
						if (FPpreIssue[0] == -1)
							FPpreIssue[0] = instrCount;
						else if (FPpreIssue[1] == -1)
							FPpreIssue[1] = instrCount;
						else if (FPpreIssue[2] == -1)
							FPpreIssue[2] = instrCount;
						else //if (preIssue[3] == -1) //optimization
							FPpreIssue[3] = instrCount;
						break;
					default: //error opcode
						return OPCODE_ERROR;
						break;
				}
				break;
			case 0xc://any other category fetch one more instruction
			case 0xe:
				if (FPpreIssue[0] == -1)
					FPpreIssue[0] = instrCount;
				else if (FPpreIssue[1] == -1)
					FPpreIssue[1] = instrCount;
				else if (FPpreIssue[2] == -1)
					FPpreIssue[2] = instrCount;
				else //if (preIssue[3] == -1) //optimization
					FPpreIssue[3] = instrCount;
				break;
			default:
				isBreak = OPCODE_ERROR;
				break;				
		}
		--preIssueFull;
	}
	return isBreak;
}

void issue(void){
	int ALUempty = 0;
	//copying current states into floating pin sets
	FPpreALU[0] = preALU[0];FPpreALU[1] = preALU[1];
	if (preALU[0] == -1) ALUempty = 2;
	else if (preALU[1] == -1) ALUempty = 1;
	switch (ALUempty) {
		case 2:
			if (preIssue[0] != -1){
				FPpreALU[0] = preIssue[0];
				FPpreIssue[0] = INSTR_USED;
			}//fall through
		case 1: 
			if (preIssue[1] != -1){
				FPpreALU[1] = preIssue[1];
				FPpreIssue[1] = INSTR_USED;
			}
			break;
		case 0:
			//queue full - stall maddi
			return;
			break;
	}
}

void mem(void){
	unsigned int instr, opcode;
	instr = preMem[0]>=0?InstrMem[preMem[0]]:-1;
	if (instr == -1) return;
	opcode = (instr & CAT1_OPCODE_MASK)>>CAT1_OPCODE_OFFSET;
	switch (opcode){
		case 0x6: //SW instruction
			DataMem[preMem[2]] = regSet[preMem[1]];// 1 - register value to be stored, 2- location to be stored at, value
			regInUse &= ~(1<<preMem[1]); //release rt for SW
			break;
		case 0x7: //LW instruction
			postMem[0] = preMem[0];//instr forwarding
			postMem[1] = preMem[1]; // 1 - destination register
			postMem[2] = DataMem[preMem[2]];// 2 - actual value to be stored is loaded using physical address passed from preMem
			break;
		default: //error opcode
			//Just because I am through :D
			break;
	}
	preMem[0] = -1;//clearing queue 
	return;
}

void wb(void){
	//postALU write back
	if (postALU[0] != -1){
		regSet[postALU[1]] = postALU[2];// 1 - destination register, 2 - value
		regInUse &= ~(1<<postALU[1]);//release rd
		postALU[0] = -1;
	}
	//postMEM write back - only for LW instr
	if (postMem[0] != -1){
		regSet[postMem[1]] = postMem[2];// 1 - destination register, 2 - value
		regInUse &= ~(1<<postMem[1]); //release rt for LW
		postMem[0] = -1;
	}
	return;
}

int execute(void){
	unsigned int instr;
	int unitReturn = 0;
	int catValue;
	int opcode;
	int rs,rt,imm_val=0;
	instr = preALU[0]>=0?InstrMem[preALU[0]]:-1;
	if (instr == -1) return unitReturn;
	catValue = (instr & CAT_MASK)>>CAT_OFFSET;
	switch (catValue){
		case 0x0: // Category 1
			opcode = (instr & CAT1_OPCODE_MASK)>>CAT1_OPCODE_OFFSET;
			switch (opcode){
				case 0x6: //SW instruction
					FPpreMem[0] = preALU[0];
					rs = (instr & CAT1_BASE_MASK)>>CAT1_BASE_OFFSET;
					FPpreMem[1] = (instr & CAT1_RT_MASK)>>CAT1_RT_OFFSET; //rt
					imm_val = (instr & IMME_MASK);
					if((imm_val & 0x00008000) == 1) imm_val = -1*(((imm_val^0xFFFFFFFF)&0x0000FFFF)+1);
					FPpreMem[2] = ((regSet[rs]+imm_val)-data_start_address)/4;
					regInUse &= ~(1<<rs); //release rs
					break;
				case 0x7: //LW instruction
					FPpreMem[0] = preALU[0];
					rs = (instr & CAT1_BASE_MASK)>>CAT1_BASE_OFFSET;
					FPpreMem[1] = (instr & CAT1_RT_MASK)>>CAT1_RT_OFFSET; //rt
					imm_val = (instr & IMME_MASK);
					if((imm_val & 0x00008000) == 1)	imm_val = -1*(((imm_val^0xFFFFFFFF)&0x0000FFFF)+1);
					FPpreMem[2] = ((regSet[rs]+imm_val)-data_start_address)/4;
					regInUse &= ~(1<<rs); //release rs
					break;
				default: //error opcode
					return OPCODE_ERROR;
					break;
			}
			break;
		case 0xc: //Category 2
			FPpostALU[0] = preALU[0];
			opcode = (instr & CAT2N3_OPCODE_MASK)>>CAT2N3_OPCODE_OFFSET;
			rs = (instr & RS_MASK)>>RS_OFFSET;
			rt = (instr & RT_MASK)>>RT_OFFSET;
			FPpostALU[1] = (instr & RD_MASK)>>RD_OFFSET; //rd
			switch (opcode){
				case 0x0: //ADD instruction
					FPpostALU[2] = regSet[rs]+regSet[rt];
					break;
				case 0x1: //SUB instruction
					FPpostALU[2] = regSet[rs]-regSet[rt];
					break;
				case 0x2: //MUL instruction
					FPpostALU[2] = regSet[rs]*regSet[rt];
					break;
				case 0x3: //AND instruction
					FPpostALU[2] = regSet[rs] & regSet[rt];
					break;
				case 0x4: //OR instruction
					FPpostALU[2] = regSet[rs] | regSet[rt];
					break;
				case 0x5: //XOR instruction
					FPpostALU[2] = regSet[rs] ^ regSet[rt];
					break;
				case 0x6: //NOR instruction
					FPpostALU[2] = ~(regSet[rs] | regSet[rt]);
					break;
				default: //error opcode
					return OPCODE_ERROR;
					break;
			}
			regInUse &= ~(1<<rs); //release rs
			regInUse &= ~(1<<rt); //release rt
			break;
		case 0xe: //Category 3
			FPpostALU[0] = preALU[0];
			opcode = (instr & CAT2N3_OPCODE_MASK)>>CAT2N3_OPCODE_OFFSET;
			rs = (instr & RS_MASK)>>RS_OFFSET;
			FPpostALU[1] = (instr & RT_MASK)>>RT_OFFSET; //rt
			imm_val = (instr & IMME_MASK);
			switch (opcode){
				case 0x0: //ADDI instruction
					if((imm_val & 0x00008000) == 1) imm_val = -1*(((imm_val^0xFFFFFFFF)&0x0000FFFF)+1);
					FPpostALU[2] = regSet[rs]+imm_val;
					break;
				case 0x1: //ANDI instruction
					FPpostALU[2] = regSet[rs] & imm_val;
					break;
				case 0x2: //ORI instruction
					FPpostALU[2] = regSet[rs] | imm_val;
					break;
				case 0x3: //XORI instruction
					FPpostALU[2] = regSet[rs] ^ imm_val;
					break;
				default: //error opcode
					return OPCODE_ERROR;
					break;
			}
			regInUse &= ~(1<<rs); //release rs
			break;
		default: //error handling
			return OPCODE_ERROR;
			break;
	}
	FPpreALU[0] = INSTR_USED;
	return unitReturn;
}

void flipLatch(void){
	int i,j,replaceMode;
	for(i=0,replaceMode =0; i<2;i++){//atmost there can be two used/issued instructions
		for(j=0;j<4;j++){
			if(FPpreIssue[j] == INSTR_USED)
				replaceMode = 1;
			if (replaceMode == 1){
				if (j != 3)
					FPpreIssue[j] = FPpreIssue[j+1];
				else
					FPpreIssue[j] = -1;
			}
		}
	}
	preIssue[0] = FPpreIssue[0];preIssue[1] = FPpreIssue[1];preIssue[2] = FPpreIssue[2];preIssue[3] = FPpreIssue[3];
	if (FPpreALU[0] == INSTR_USED){//If there is a used instr it has to be at the top
		FPpreALU[0] = FPpreALU[1];
		FPpreALU[1] = -1;
	}
	preALU[0] = FPpreALU[0];preALU[1] = FPpreALU[1];
	preMem[0] = FPpreMem[0];preMem[1] = FPpreMem[1];preMem[2] = FPpreMem[2];
	postALU[0] = FPpostALU[0];postALU[1] = FPpostALU[1];postALU[2] = FPpostALU[2];
	postMem[0] = FPpostMem[0];postMem[1] = FPpostMem[1];postMem[2] = FPpostMem[2];
}

int simMIPS(int data_start_address){
	FILE *simfile;
	int clock = 1;
	int isBreak =0;
	int unitReturn;
	int dataCount,regCount;
	simfile = fopen("simulation.txt", "w");
	if (!simfile) {
		printf("Invalid file name / file open error");
		return 1;
	}
	PC = 0;
	do{
		isBreak = fetch();
		issue();
		unitReturn = execute();
		mem();
		wb();
		flipLatch();
		if (isBreak == OPCODE_ERROR || unitReturn == OPCODE_ERROR)
		{
			fprintf(simfile, "Unimplemented opcode is used. This opcode is reserved.");
			return OPCODE_ERROR;
		}
		//printing of file starts
		fprintf(simfile, "--------------------\nCycle:%d\n\n",clock++);
		fprintf(simfile, "IF Unit:\n\tWaiting Instruction:[%s]\n\tExecuted Instruction:[%s]\n",
				InstrStr[waitInstr<0?(MEMORY_SIZE-1):waitInstr],InstrStr[execInstr<0?(MEMORY_SIZE-1):execInstr]);
		fprintf(simfile, "Pre-Issue Queue:\n\tEntry 0:[%s]\n\tEntry 1:[%s]\n\tEntry 2:[%s]\n\tEntry 3:[%s]\n",
				InstrStr[preIssue[0]<0?(MEMORY_SIZE-1):preIssue[0]],InstrStr[preIssue[1]<0?(MEMORY_SIZE-1):preIssue[1]],
				InstrStr[preIssue[2]<0?(MEMORY_SIZE-1):preIssue[2]],InstrStr[preIssue[3]<0?(MEMORY_SIZE-1):preIssue[3]]);
		fprintf(simfile, "Pre-ALU Queue:\n\tEntry 0:[%s]\n\tEntry 1:[%s]\n",
				InstrStr[preALU[0]<0?(MEMORY_SIZE-1):preALU[0]],InstrStr[preALU[1]<0?(MEMORY_SIZE-1):preALU[1]]);
		fprintf(simfile, "Pre-MEM Queue:[%s]\nPost-MEM Queue:[%s]\nPost-ALU Queue:[%s]\n\n",
				InstrStr[preMem[0]<0?(MEMORY_SIZE-1):preMem[0]],InstrStr[postMem[0]<0?(MEMORY_SIZE-1):postMem[0]],InstrStr[postALU[0]<0?(MEMORY_SIZE-1):postALU[0]]);
		fprintf(simfile, "Registers\n");
		regCount =0; 
		while(regCount != 32){
			if(regCount%8 ==0) fprintf(simfile,"R%02d:\t",regCount);
			if((regCount+1)%8==0) fprintf(simfile,"%d\n",regSet[regCount++]);
			else fprintf(simfile,"%d\t",regSet[regCount++]);
		}
		fprintf(simfile, "\nData\n");
		dataCount =0;
		while(dataCount != dataLength){
			if(dataCount%8 ==0) fprintf(simfile,"%d:\t",data_start_address+4*dataCount);
			if((dataCount+1)%8==0) fprintf(simfile,"%d\n",DataMem[dataCount++]);
			else fprintf(simfile,"%d\t",DataMem[dataCount++]);
		}
	}while(isBreak != 1);
	fprintf(simfile, "\n");
	fclose(simfile);
	return 0;
}

int genInstrStr(unsigned int iword, char retStr[]){
	int catValue = (iword & CAT_MASK)>>CAT_OFFSET;
	int opcode =0;
	int bufoffset =0;
	int rs,rd,rt,imm_val=0;
	switch (catValue){
		case 0x0: // Category 1
			opcode = (iword & CAT1_OPCODE_MASK)>>CAT1_OPCODE_OFFSET;
			switch (opcode){
				case 0x0: //J instruction
					imm_val = (iword & 0x03FFFFFF)<<2;
					snprintf(retStr, 32, "J #%d", imm_val);
					break;
				case 0x2: //BEQ instruction
					rs = (iword & CAT1_BASE_MASK)>>CAT1_BASE_OFFSET;
					rt = (iword & CAT1_RT_MASK)>>CAT1_RT_OFFSET;
					imm_val = (iword & IMME_MASK)<<2;
					if((imm_val & 0x00020000) == 1) imm_val = -1*(((imm_val^0xFFFFFFFF)&0x0003FFFF)+1);
					snprintf(retStr, 32, "BEQ R%d, R%d, #%d", rs, rt, imm_val);
					break;
				case 0x4: //BGTZ instruction
					rs = (iword & CAT1_BASE_MASK)>>CAT1_BASE_OFFSET;
					imm_val = (iword & IMME_MASK)<<2;
					if((imm_val & 0x00020000) == 1)	imm_val = -1*(((imm_val^0xFFFFFFFF)&0x0003FFFF)+1);
					snprintf(retStr, 32, "BGTZ R%d, #%d", rs, imm_val);
					break;
				case 0x5: //BREAK instruction
					snprintf(retStr, 32, "BREAK");
					return 1;
					break;
				case 0x6: //SW instruction
					rs = (iword & CAT1_BASE_MASK)>>CAT1_BASE_OFFSET;
					rt = (iword & CAT1_RT_MASK)>>CAT1_RT_OFFSET;
					imm_val = (iword & IMME_MASK);
					if((imm_val & 0x00008000) == 1) imm_val = -1*(((imm_val^0xFFFFFFFF)&0x0000FFFF)+1);
					snprintf(retStr, 32, "SW R%d, %d(R%d)", rt, imm_val, rs);
					break;
				case 0x7: //LW instruction
					rs = (iword & CAT1_BASE_MASK)>>CAT1_BASE_OFFSET;
					rt = (iword & CAT1_RT_MASK)>>CAT1_RT_OFFSET;
					imm_val = (iword & IMME_MASK);
					if((imm_val & 0x00008000) == 1) imm_val = -1*(((imm_val^0xFFFFFFFF)&0x0000FFFF)+1);
					snprintf(retStr, 32, "LW R%d, %d(R%d)", rt, imm_val, rs);
					break;
				default: //error opcode
					printf("Unimplemented opcode in category 1 used. This opcode is reserved.");
					break;
			}
			break;
		case 0xc: //Category 2
			opcode = (iword & CAT2N3_OPCODE_MASK)>>CAT2N3_OPCODE_OFFSET;
			switch (opcode){
				case 0x0: //ADD instruction
					bufoffset = snprintf(retStr, 32, "ADD ");
					break;
				case 0x1: //SUB instruction
					bufoffset = snprintf(retStr, 32, "SUB ");
					break;
				case 0x2: //MUL instruction
					bufoffset = snprintf(retStr, 32, "MUL ");
					break;
				case 0x3: //AND instruction
					bufoffset = snprintf(retStr, 32, "AND ");
					break;
				case 0x4: //OR instruction
					bufoffset = snprintf(retStr, 32, "OR ");
					break;
				case 0x5: //XOR instruction
					bufoffset = snprintf(retStr, 32, "XOR ");
					break;
				case 0x6: //NOR instruction
					bufoffset = snprintf(retStr, 32, "NOR ");
					break;
				default: //error opcode
					printf("Unimplemented opcode in category 2 used. This opcode is reserved.");
					break;
			}
			rs = (iword & RS_MASK)>>RS_OFFSET;
			rt = (iword & RT_MASK)>>RT_OFFSET;
			rd = (iword & RD_MASK)>>RD_OFFSET;
			snprintf(retStr+bufoffset, 32-bufoffset, "R%d, R%d, R%d", rd, rs, rt);
			break;
		case 0xe: //Category 3
			opcode = (iword & CAT2N3_OPCODE_MASK)>>CAT2N3_OPCODE_OFFSET;
			switch (opcode){
				case 0x0: //ADDI instruction
					bufoffset = snprintf(retStr, 32, "ADDI ");
					break;
				case 0x1: //ANDI instruction
					bufoffset = snprintf(retStr, 32, "ANDI ");
					break;
				case 0x2: //ORI instruction
					bufoffset = snprintf(retStr, 32, "ORI ");
					break;
				case 0x3: //XORI instruction
					bufoffset = snprintf(retStr, 32, "XORI ");
					break;
				default: //error opcode
					printf("Unimplemented opcode in category 3 used. This opcode is reserved.");
					break;
			}
			rs = (iword & RS_MASK)>>RS_OFFSET;
			rt = (iword & RT_MASK)>>RT_OFFSET;
			imm_val = (iword & IMME_MASK);
			if((imm_val & 0x00008000) == 1){
				imm_val = ((imm_val^0xFFFFFFFF)&0x0000FFFF)+1;
				snprintf(retStr+bufoffset, 32-bufoffset, "R%d, R%d, #-%d", rt, rs, imm_val);
			}
			else
				snprintf(retStr+bufoffset, 32-bufoffset, "R%d, R%d, #%d", rt, rs, imm_val);
			break;
		default: //error handling
			printf("Unimplemented opcode category used. This opcode is reserved.");
			break;
	}
	return 0; // regular instruction	
}

int main(int argc, char* argv[])
{
	FILE *infile;
	//FILE *disfile; //Disassembly
	char c;
	unsigned int instrword = 0;
	int shiftby=0;
	int prgMem_address = 128;
	unsigned char break_reached = 0; 
	int dataMem_address =0;
	char retStr[32]; //19 would be enough, but 32 is a nice number :D
	
	if(argc != 2){
		printf("Incorrect input arguments");
		return 1;
	}
	infile = fopen(argv[1], "r");
	if (!infile) {
		printf("Invalid file name / file open error");
		return 1;
	}
	//disfile = fopen("disassembly.txt", "w");//Disassembly
	//if (!disfile) {
		//printf("Invalid file name / file open error");
		//return 1;
	//}
	
	while ((c = getc(infile)) != EOF){
		if ('0' == c || '1' == c){
			instrword <<= shiftby;
			instrword |= (c=='0'? 0x00000000 : 0x00000001);
			//fputc(c, disfile);//Disassembly
			shiftby=1;
			continue;
		}
		else if('\r' == c) continue;
		else if('\n' == c) {
			if(break_reached == 0){ //break not yet reached, program memeory active
				break_reached = genInstrStr(instrword, retStr);
				//fprintf(disfile, "\t%d\t%s\n", prgMem_address, retStr);//Disassembly
				strcpy(InstrStr[instrLength],retStr);
				InstrMem[instrLength++]=instrword;
			}
			else { //break reached now in data memory
				if(dataMem_address == 0) dataMem_address = prgMem_address;
				//fprintf(disfile, "\t%d\t%d\n", prgMem_address, instrword);//Disassembly
				DataMem[dataLength++]=instrword;
			}
			prgMem_address+=4;
			instrword = 0;
			shiftby =0;
		}      
	}
	//last memory instruction according to sample input.txt
	//fprintf(disfile, "\t%d\t%d\n", prgMem_address, instrword);//Disassembly
	DataMem[dataLength++]=instrword; //Additional data entry was reported as error
	fclose(infile);
	//fclose(disfile);//Disassembly
	return simMIPS(dataMem_address); 
}