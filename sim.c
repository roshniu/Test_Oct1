/*
 * sim.c
 * All rights reserved.
 *
 *  Created on: Oct 19, 2013
 *      Author: damon stachler, roshni uppala
 */

#include <stdio.h>
#include <string.h>
#include <stdbool.h>
#include <execinfo.h>
#include <signal.h>
#include <stdlib.h>
#include <unistd.h>
#include "globals.h"

struct instruction inst_mem[MAX_LINES_OF_CODE];
struct instruction IR[16];
struct pipeline_buffer{ //pipeline buffer
	char *op;
	char *operands;
	int valid;
	int fetch_cycle;
	int branch_taken;
	int branch_prediction;
	struct instruction IR_buf;  //Instruction for the buffer
	int total_no_instr_fetched;
}IF_ID[16],ID_DIS[16],DIS_ISS[16],ISS_EX[16],EX_COM[16],IF,ID,DIS;

int code_length;
int SW; // Superscalar width
int BTB_size; // Branch target buffer size
int BTB_tail = -1;
int RS_entries; // NUmber of Reservation entries
int FU_no; // Number of functional units
int BTB[100];

int RRF_no; // Number of renaming buffer entries
int ROB_no; // Number of reorder buffer entries
int L1_hitrate; // L1 cache hitrate
int L2_hitrate; // L2 cache hitrate
int L1_time; // L1 cache access time
int L2_time; // L2 cache access time
char filename[15]; // Filename of trace file
int MEM_time;   // Memmory access time
int L1_data_hitrate;
int L1_data_miss = 0;
int L2_data_miss = 0;
int L1_data_time=1;

int L1_miss = 0;
int L2_miss = 0;
int fetch_flag=0;
int k=0;

FILE *fpt;
char *Fetch_Array[20];
char *Decode_Array[20];
bool done = false;
char	opcode[20],operands[40],label[20];
struct instruction Decode_inst[16];
struct RRF_table RRF[512];// renaming register file
struct ARF_table ARF[65]; // architecture register file
struct RS_table RS_int[513], RS_fpp[513], RS_mem[513], RS_br[513]; // reservation stations
struct ROB_table ROB[513]; // reorder buffer
struct FU_block FU_int[8],FU_fpp[8],FU_mem[8],FU_br[1]; //functional units
struct DISPATCH_TABLE DISPATCH[513]; // dispatch bbufer
struct FETCH_TABLE FETCH[513]; // fetching buffer

int head_rob=-1;
int tail_rob=-1;
int head_rs_mem=-1;
int tail_rs_mem=-1;
int head_dispatch=-1;
int tail_dispatch=-1;
int head_fetch=-1;
int tail_fetch=-1;

int if_valid = 1;
int id_valid = 0;
int dis_valid = 0;
int iss_valid = 0;
int ex_valid = 0;
int com_valid = 0;
int i;
int a,b,c;
int ptr_rob,ptr_rrf,ptr_RS_int,ptr_RS_fpp,ptr_RS_br;
int src_value1,src_value2,src_imm;
int ref_rrf_tag;
int available_rob,available_rrf,available_rs_int,available_rs_fpp,available_rs_mem,available_rs_br;
int index_to_arf;
int IR_inserted_flag=0;

int total_branches = 0;
int correct_predictions = 0;

fpos_t *pos;


//gshare variables
unsigned int default_pc;
unsigned int pc_value;
int pc_and,pc_shift,offset_addr,br_pred_bit;
int br_pred;
unsigned int bhsr=0;
int x;
int rob_overflow_stall = 0;
int rs_mem_overflow_stall = 0;
int fetch_overflow=0;
int dispatch_overflow_stall = 0;


int l1_fetch_cycle=0;
int l2_fetch_cycle=0;
int mem_fetch_cycle=0;
int total_fetch_cycle=0;
int total_no_instr_fetched=0;
int counter=0;
int instr_to_fetch=0;

int wait_L1=0;
int wait_L2=0;
int wait_Mem=0;
int fetch_time = 0;
int cycles = 0;
int finished_instructions = 0;
double IPC;

int fu_int_utilization=0;
int fu_fpp_utilization=0;
int fu_mem_utilization=0;
int fu_br_utilization=0;
int rs_int_utilization=0;
int rs_fpp_utilization=0;
int rs_mem_utilization=0;
int rs_br_utilization=0;
int rob_utilization=0;
int rrf_utilization=0;
//initializing the gshare predictor to 2
int gshare[1024] = {2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
		   2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
		   2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
		   2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
		   2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
 		   2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
		   2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
		   2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
		   2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
		   2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
		   2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
		   2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
		   2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
		   2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
		   2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
 		   2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
		   2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
		   2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
		   2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
		   2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
		   2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2};

void handler(int sig)
{
	void *array[10];
	size_t size;

	size = backtrace(array,10);

	fprintf(stderr, "Error: signal %d:\n", sig);
	backtrace_symbols_fd(array, size, STDERR_FILENO);
	exit(1);
}




/* ****** MAIN FUNCTION *********/

int main(int argc, char **argv)
{
	int bb;
	/* FILENAME FROM THE USER */
	printf("Enter the trace filename");
	scanf("%s",&filename);
	argv[1]=filename;
	argc=2;


	//signal(SIGSEGV, handler);
	if ((fpt=fopen(argv[1],"r")) == NULL)
	{
  		printf("Unable to open %s for reading\n",argv[1]);
  		exit(0);
  	}
	 /* superscalar factor*/
		printf("Enter the superscalar factor [1-16] : \t ");
		scanf("%d",&SW);

		 /* Branch target buffer size*/
		printf("Enter the Branch target buffer entry size[ ] : \t ");
		scanf("%d",&BTB_size);

		   /* NUmber of reservation entries */
		printf("Enter the number of reservation station entries [1-8 ]: \t");
		scanf("%d",&RS_entries);

		 /* Number of functional units*/
		printf("Enter the number of Integer, floating point, Memory functional units[1-8] : \t");
		scanf("%d",&FU_no);

		 /*NUmber of renaming table entries*/
		printf("Enter the number of renaming table entries[1-512] : \t");
		scanf("%d",&RRF_no);

		 /*Number of Reorder Buffer Entries*/
		printf("Enter the number of Reorder Buffer entries [1-512] : \t");
		scanf("%d",&ROB_no);

	    /*L1 instruction cache hit rate */
		printf ("Enter L1 instruction cache hit rate [1-100] : \t");
		scanf("%d",&L1_hitrate);

		 /*L2 cache hit rate */
		printf("Enter L2 cache hit rate [1-100] : \t");
		scanf("%d",&L2_hitrate);

	 /*L1 cache latency (access time)*/
		printf("Enter L1 cache latency(access time) [1-100] : \t");
		scanf("%d",&L1_time);

		 /*L2 cache latency (access time) */
		printf("Enter L2 cache latency(access time)[1-100] : \t");
		scanf("%d",&L2_time);

		/*L1 data cache hit rate */
		printf("Enter L1 data cache hit rate [1-100] : \t");
		scanf("%d",&L1_data_hitrate);

		/* L1 data cache access time */
		printf("Enter L1 data cache access time [1-100] : \t");
		scanf("%d",&L1_data_time);

		/* Main Memory access time */
		printf("Enter main memory access time [1-100] : \5");
		scanf("%d",&MEM_time);

	for(i=0;i<16;i++)
	{
		IF_ID[i].op = (char*)malloc(15);
		IF_ID[i].operands = (char*)malloc(50);
		FETCH[i].op=(char*)malloc(15);
		FETCH[i].operands=(char*)malloc(50);
	}

	while(done != true)
	{
		Commit();
		Execute();
		Issue();
		Dispatch();
		Decode();
		Fetch();
		cycles = cycles + 1;
		for(bb=0; bb<FU_no; bb++)
		{
			if(FU_int[bb].busy == 1)
				fu_int_utilization += 1;
			if(FU_fpp[bb].busy == 1)
				fu_fpp_utilization += 1;
			if(FU_mem[bb].busy == 1)
				fu_mem_utilization += 1;
		}
		if(FU_br[0].busy == 1)
			fu_br_utilization += 1;
		for(bb=0; bb<RS_entries; bb++)
		{
			if(RS_int[bb].busy == 1)
				rs_int_utilization += 1;
			if(RS_fpp[bb].busy == 1)
				rs_fpp_utilization += 1;
			if(RS_mem[bb].busy == 1)
				rs_mem_utilization += 1;
			if(RS_br[bb].busy == 1)
				rs_br_utilization += 1;
		}
		for(bb=0; bb<RRF_no; bb++)
		{
			if(RRF[bb].busy == 1)
				rrf_utilization += 1;
		}
		for(bb=0; bb<ROB_no; bb++)
		{
			if(ROB[bb].busy == 1)
				rob_utilization +=1;
		}
	}

	while(head_dispatch != -1)
	{
		Commit();
		Execute();
		Issue();
		Dispatch();
		Decode();
		cycles = cycles + 1;
		for(bb=0; bb<FU_no; bb++)
		{
			if(FU_int[bb].busy == 1)
				fu_int_utilization += 1;
			if(FU_fpp[bb].busy == 1)
				fu_fpp_utilization += 1;
			if(FU_mem[bb].busy == 1)
				fu_mem_utilization += 1;
		}
		if(FU_br[0].busy == 1)
			fu_br_utilization += 1;
		for(bb=0; bb<RS_entries; bb++)
		{
			if(RS_int[bb].busy == 1)
				rs_int_utilization += 1;
			if(RS_fpp[bb].busy == 1)
				rs_fpp_utilization += 1;
			if(RS_mem[bb].busy == 1)
				rs_mem_utilization += 1;
			if(RS_br[bb].busy == 1)
				rs_br_utilization += 1;
		}
		for(bb=0; bb<RRF_no; bb++)
		{
			if(RRF[bb].busy == 1)
				rrf_utilization += 1;
		}
		for(bb=0; bb<ROB_no; bb++)
		{
			if(ROB[bb].busy == 1)
				rob_utilization +=1;
		}
	}

	while(head_rob != -1)
	{
		Commit();
		Execute();
		Issue();
		cycles = cycles + 1;
		for(bb=0; bb<FU_no; bb++)
		{
			if(FU_int[bb].busy == 1)
				fu_int_utilization += 1;
			if(FU_fpp[bb].busy == 1)
				fu_fpp_utilization += 1;
			if(FU_mem[bb].busy == 1)
				fu_mem_utilization += 1;
		}
		if(FU_br[0].busy == 1)
			fu_br_utilization += 1;
		for(bb=0; bb<RS_entries; bb++)
		{
			if(RS_int[bb].busy == 1)
				rs_int_utilization += 1;
			if(RS_fpp[bb].busy == 1)
				rs_fpp_utilization += 1;
			if(RS_mem[bb].busy == 1)
				rs_mem_utilization += 1;
			if(RS_br[bb].busy == 1)
				rs_br_utilization += 1;
		}
		for(bb=0; bb<RRF_no; bb++)
		{
			if(RRF[bb].busy == 1)
				rrf_utilization += 1;
		}
		for(bb=0; bb<ROB_no; bb++)
		{
			if(ROB[bb].busy == 1)
				rob_utilization +=1;
		}
	}

	// calculation of IPC and resource utilizations
	finished_instructions = finished_instructions - 1; // number of finished instructions
	IPC = (double)finished_instructions/(double)cycles;
	printf("Total Cycles: %d Finished Instructions: %d IPC: %2.4f\n", cycles, finished_instructions, IPC);
	printf("Branch Prediction Rate %2.2f\%\n", ((float)correct_predictions/total_branches)*100);
	printf("FU_int utilization %2.4f\%\n", (((double)fu_int_utilization/(double)cycles)/(double)FU_no)*100.00);
	printf("FU_fpp utilization %2.4f\%\n", (((double)fu_fpp_utilization/(double)cycles)/(double)FU_no)*100.00);
	printf("FU_mem utilization %2.4f\%\n", (((double)fu_mem_utilization/(double)cycles)/(double)FU_no)*100.00);
	printf("FU_br utilization %2.4f\%\n", (((double)fu_br_utilization/(double)cycles)/(double)1)*100.00);
	printf("RS_int utilization %2.4f\%\n", (((double)rs_int_utilization/(double)cycles)/(double)RS_entries)*100.00);
	printf("RS_fpp utilization %2.4f\%\n", (((double)rs_fpp_utilization/(double)cycles)/(double)RS_entries)*100.00);
	printf("RS_mem utilization %2.4f\%\n", (((double)rs_mem_utilization/(double)cycles)/(double)RS_entries)*100.00);
	printf("RS_br utilization %2.4f\%\n", (((double)rs_br_utilization/(double)cycles)/(double)RS_entries)*100.00);
	printf("RRF utilization %2.4f\%\n", (((double)rrf_utilization/(double)cycles)/(double)RRF_no)*100.00);
	printf("ROB utilization %2.4f\%\n", (((double)rob_utilization/(double)cycles)/(double)ROB_no)*100.00);

	for(i=0;i<16;i++)
	{
		free(IF_ID[i].op);
		free(IF_ID[i].operands);
		free(FETCH[i].op);
		free(FETCH[i].operands);
	}

	return 0;
}

Branch_Prediction(char *opcode, int index)  // gshare branch predictor with branch target buffer
{
	char input[81], line[81];
	char *field1, *field2, *field3;
	int nextPC;
	int gshare_index;
	int ii;

	if(strcmp(opcode,"j")==0 || strcmp(opcode,"jal")==0 || strcmp(opcode,"jr")==0 || strcmp(opcode,"jalr")==0 || strcmp(opcode,"beq")==0 ||
	strcmp(opcode,"bne")==0 || strcmp(opcode,"blez")==0 || strcmp(opcode,"bgtz")==0 || strcmp(opcode,"bltz")==0 || strcmp(opcode,"bgez")==0 ||
	strcmp(opcode,"bc1f")==0 || strcmp(opcode,"bc1t")==0)
	{
		total_branches += 1;
		if(feof(fpt))
		{
			IF_ID[index].branch_taken = 0;
			IF_ID[index].branch_prediction = 0;
			gshare_index = ((IF_ID[index].IR_buf.PC&0x3FF) >> 3) ^ bhsr;
			if(gshare[gshare_index] == 0 || gshare[gshare_index] == 1)
				IF_ID[index].branch_prediction = 0;
			else if(gshare[gshare_index] == 2 || gshare[gshare_index] == 3)
				IF_ID[index].branch_prediction = 1;

			if(BTB_tail == -1)
			{
				//PC not in BTB branch mispredicted
			}
			else
			{
				for(ii=0; ii<BTB_tail; ii++)
				{
					if(BTB[ii] == IF_ID[index].IR_buf.PC)
					{
						if(IF_ID[index].branch_taken == IF_ID[index].branch_prediction)
						{
							correct_predictions += 1;
							break;
						}
					}
				}
			}
		}
		else
		{
			fgetpos(fpt,&pos);
			fgets(input,80,fpt);
			strcpy(line,input);
			ParseLineIntoTokens(line," \t\n",&field1,&field2,&field3);
			nextPC = atoi(field1);
			if(IF_ID[index].IR_buf.PC+8 == nextPC)
			{
				IF_ID[index].branch_taken = 0;
			}
			else
			{
				IF_ID[index].branch_taken = 1;
			}
			gshare_index = ((IF_ID[index].IR_buf.PC&0x3FF) >> 3) ^ bhsr;
			if(gshare[gshare_index] == 0 || gshare[gshare_index] == 1)
				IF_ID[index].branch_prediction = 0;
			else if(gshare[gshare_index] == 2 || gshare[gshare_index] == 3)
				IF_ID[index].branch_prediction = 1;

			if(BTB_tail == -1)
			{
				//PC not in BTB branch mispredicted
			}
			else
			{
				for(ii=0; ii<BTB_tail; ii++)
				{
					if(BTB[ii] == IF_ID[index].IR_buf.PC)
					{
						if(IF_ID[index].branch_taken == IF_ID[index].branch_prediction)
						{
							correct_predictions += 1;
							break;
						}
					}
				}
			}


			fsetpos(fpt,&pos);
		}
	}
}

/*----------------------------------------------------------------------------------------------*/
/*************Fetch Stage****************************/
void Fetch()
/* Fetches the instruction with there address. Fetch group is decided based on the superscalar width given by the user*/

{

	tail_fetch=-1;
	head_fetch=-1;

	int flag=0;
	total_no_instr_fetched=0;
	char *field1, *field2, *field3;
	char input[81], line[81];


	if(rob_overflow_stall == 1 || rs_mem_overflow_stall == 1 || dispatch_overflow_stall == 1)
	{
		// stall since overflows
	}
	else
	{
		i=0;
	if(counter==0)
	{
		while(i !=SW) // generating hit or miss depending on random number

		{
			if((rand()%100)<= L1_hitrate)
			{
				FETCH[i].L1_hit=1;
				FETCH[i].L2_hit=0;
			}


			if(((rand()%100)<= L2_hitrate)&&(FETCH[i].L1_hit!=1))
			{
				FETCH[i].L1_hit=0;
				FETCH[i].L2_hit=1;

			}
			if((FETCH[i].L1_hit!=1)&&(FETCH[i].L2_hit!=1))
			{
				FETCH[i].L1_hit=0;
				FETCH[i].L2_hit=0;
				FETCH[i].mem_hit=1;
			}
			i++;
			counter++;
		}
	}

	if(instr_to_fetch<SW)
	{
		i=instr_to_fetch;
	}
	else
		i=0;

	loop1:
		while((i !=SW))
		{
			if(FETCH[i].L1_hit==1) // l1 cache hit?
			{

				if(wait_L1>=L1_time)
				{
					while(fgets(input,80,fpt)!=NULL)
					{
					strcpy(line,input);
					ParseLineIntoTokens(line," \t\n",&field1,&field2,&field3);
					FETCH[i].IR_buf.PC = atoi(field1);
					strncpy(FETCH[i].op,field2,strlen(field2)+1);
					if(field3 != NULL)
						strncpy(FETCH[i].operands,field3,strlen(field3)+1);
					FETCH[i].valid = if_valid;
					FETCH[i].IR_buf.fetch_time=fetch_time;
					fetch_time = fetch_time + 1;
					flag=1;
					i++;
					total_no_instr_fetched++;
					goto loop1;
					}
				}
				else
				{
					wait_L1++;
					goto control1;
				}

			}

			else if((FETCH[i].L1_misscount!=1)&&(FETCH[i].L2_misscount!=1))
			{
				FETCH[i].L1_misscount=1;

				goto control1;
			}

			if((FETCH[i].L1_misscount==1)&&(FETCH[i].L2_hit==1))
			{


				if(wait_L2>=L2_time)
				{

					strcpy(line,input);
					ParseLineIntoTokens(line," \t\n",&field1,&field2,&field3);
					FETCH[i].IR_buf.PC = atoi(field1);
					strncpy(FETCH[i].op,field2,strlen(field2)+1);
					if(field3 != NULL)
						strncpy(FETCH[i].operands,field3,strlen(field3)+1);
					FETCH[i].valid = if_valid;
					FETCH[i].IR_buf.fetch_time= fetch_time;
					fetch_time = fetch_time + 1;
					i++;
					flag=1;
					continue;
					total_no_instr_fetched++;
				}
			else
				{
					wait_L2++;
					l2_fetch_cycle=L1_time+L2_time;
					goto control1;
				}
			}

			else if(FETCH[i].L2_misscount!=1)

			{
				FETCH[i].L1_misscount=0;
				FETCH[i].L2_misscount=1;
				l2_fetch_cycle=L2_time;
				goto control1;
			}

			if((FETCH[i].L2_misscount==1)&&(FETCH[i].L1_hit==0)&&(FETCH[i].L2_hit==0))
			{

				//mem:
				if(wait_Mem>=MEM_time)
				{

					FETCH[i].L1_misscount=0;
					FETCH[i].L2_misscount=0;
					Fetch_Array[i] = input;
					strcpy(line,input);
					ParseLineIntoTokens(line," \t\n",&field1,&field2,&field3);
					FETCH[i].IR_buf.PC = atoi(field1);
					strncpy(FETCH[i].op,field2,strlen(field2)+1);
					if(field3 != NULL)
						strncpy(FETCH[i].operands,field3,strlen(field3)+1);
					FETCH[i].valid = if_valid;
					FETCH[i].IR_buf.fetch_time=fetch_time;
					fetch_time = fetch_time+1;
					i++;
					flag=1;
					total_no_instr_fetched++;
				}
				else
				{
					wait_Mem++;
					goto control1;
				}
			}

			control1:

			instr_to_fetch=i;
			goto control2;
		}


		if(wait_L1==L1_time)
			wait_L1=0;
		if(wait_L2==L1_time)
			wait_L2=0;
		if(wait_L2==MEM_time)
			wait_Mem=0;

		if(i==SW)
			counter=0;

		if(instr_to_fetch==SW)
			counter=0;

		control2:
		IF.total_no_instr_fetched=total_no_instr_fetched;
		if(flag==1)
		{
		for(i=0;i<total_no_instr_fetched;i++)
			{

				if((tail_fetch+1)%SW==head_fetch)
				{
					printf("Fetch in IFID overflow");
					fetch_overflow=1;
				}
				else if(head_fetch== -1)
				{
					head_fetch=tail_fetch=0;
					goto X1;
				}
				else                		// adding instructions into rob buffer
				{//x
					tail_fetch=(tail_fetch+1)%SW;
					X1:
					strcpy(IF_ID[tail_fetch].op,FETCH[i].op);
					strcpy(IF_ID[tail_fetch].operands,FETCH[i].operands);
					IF_ID[tail_fetch].IR_buf.PC = FETCH[i].IR_buf.PC;
					IF_ID[tail_fetch].valid = FETCH[i].valid;
					IF_ID[tail_fetch].IR_buf.fetch_time = FETCH[i].IR_buf.fetch_time;
					Branch_Prediction(IF_ID[tail_fetch].op, tail_fetch);

				}
			}

		}
		if(feof(fpt))
			done = true;
	}
}







/* --------------------------------------------------------------------------------------------------*/
/**************************Decode Stage*************************************************************/

void Decode()
/* identifies the instruction types and separates them into there sources and register destination and operands */



{
	int insert;
	int available_dispatch;
	char *field1, *field2, *field3, *oper1, *oper2, *oper3;
	if(rob_overflow_stall == 1 || rs_mem_overflow_stall == 1 || dispatch_overflow_stall)
	{
	}
	else
	{
		for(i=0; i < IF.total_no_instr_fetched; i++)
		{
			id_valid = IF_ID[i].valid;
			if(id_valid == 0)
			{
			}
			else
			{

				field2 = IF_ID[i].op;
				field3 = IF_ID[i].operands;

				if (field2 == NULL)
    				{
   					printf("Too few fields on the following line:\n");
    					exit(0);
    				}
  				if (field3 != NULL)
    				{	/* program line had label */
    					strcpy(opcode,field2);
    					strcpy(operands,field3);
    				}
				if((strcmp(field2,"syscall") == 0) || (strcmp(field2,"nop") == 0))
				{
					if(strcmp(field2,"syscall") == 0)
					{
						Decode_inst[i].op = syscall;
						Decode_inst[i].d = -1;
						Decode_inst[i].s1 = -1;
						Decode_inst[i].s2 = -1;
						Decode_inst[i].imm = -1;
					}
					else if(strcmp(field2,"nop") == 0)
					{
						Decode_inst[i].op = nop;
						Decode_inst[i].d = -1;
						Decode_inst[i].s1 = -1;
						Decode_inst[i].s2 = -1;
						Decode_inst[i].imm = -1;
					}
				}
				else
				{
					ParseLineIntoTokens(operands,",",&oper1,&oper2,&oper3);

					if((strcmp(opcode, "and") == 0) || (strcmp(opcode, "or") == 0) || (strcmp(opcode, "add") == 0) || (strcmp(opcode, "addu") == 0) ||
						(strcmp(opcode, "sub") == 0) || (strcmp(opcode, "subu") == 0) || (strcmp(opcode, "xor") == 0) || (strcmp(opcode, "nor") == 0) ||
						(strcmp(opcode, "sllv") == 0) || (strcmp(opcode, "srlv") == 0) || (strcmp(opcode, "srav") == 0) || (strcmp(opcode, "slt") == 0) ||
						(strcmp(opcode, "sltu") == 0))
					{
						if(strcmp(opcode, "and") == 0)
							Decode_inst[i].op = and;
						else if(strcmp(opcode, "or") == 0)
							Decode_inst[i].op = or;
						else if(strcmp(opcode, "add") == 0)
							Decode_inst[i].op = add;
						else if(strcmp(opcode, "addu") == 0)
							Decode_inst[i].op = addu;
						else if(strcmp(opcode, "sub") == 0)
							Decode_inst[i].op = sub;
						else if(strcmp(opcode, "subu") == 0)
							Decode_inst[i].op = subu;
						else if(strcmp(opcode, "xor") == 0)
							Decode_inst[i].op = xor;
						else if(strcmp(opcode, "nor") == 0)
							Decode_inst[i].op = nor;
						else if(strcmp(opcode, "sllv") == 0)
							Decode_inst[i].op = sllv;
						else if(strcmp(opcode, "srlv") == 0)
							Decode_inst[i].op = srlv;
						else if(strcmp(opcode, "srav") == 0)
							Decode_inst[i].op = srav;
						else if(strcmp(opcode, "slt") == 0)
							Decode_inst[i].op = slt;
						else if(strcmp(opcode, "sltu") == 0)
							Decode_inst[i].op = sltu;

						ParseRegister(oper1,&(Decode_inst[i].d));
						ParseRegister(oper2,&(Decode_inst[i].s1));
						ParseRegister(oper3,&(Decode_inst[i].s2));
						Decode_inst[i].imm=-1;
						//printf("Op: %d %d %d %d\n", Decode_inst[i].op, Decode_inst[i].d, Decode_inst[i].s1, Decode_inst[i].s2);
					}
					else if((strcmp(opcode, "addi") == 0) || (strcmp(opcode, "addiu") == 0) || (strcmp(opcode, "andi") == 0) || (strcmp(opcode, "ori") == 0) ||
						(strcmp(opcode, "xori") == 0) || (strcmp(opcode, "sll") == 0) || (strcmp(opcode, "srl") == 0) || (strcmp(opcode, "sra") == 0) ||
						(strcmp(opcode, "slti") == 0) || (strcmp(opcode, "sltiu") == 0))
					{
						if(strcmp(opcode, "addi") == 0)
							Decode_inst[i].op = addi;
						else if(strcmp(opcode, "addiu") == 0)
							Decode_inst[i].op = addiu;
						else if(strcmp(opcode, "andi") == 0)
							Decode_inst[i].op = andi;
						else if(strcmp(opcode, "ori") == 0)
							Decode_inst[i].op = ori;
						else if(strcmp(opcode, "xori") == 0)
							Decode_inst[i].op = xori;
						else if(strcmp(opcode, "sll") == 0)
							Decode_inst[i].op = sll;
						else if(strcmp(opcode, "srl") == 0)
							Decode_inst[i].op = srl;
						else if(strcmp(opcode, "sra") == 0)
							Decode_inst[i].op = sra;
						else if(strcmp(opcode, "slti") == 0)
							Decode_inst[i].op = slti;
						else if(strcmp(opcode, "sltiu") == 0)
							Decode_inst[i].op = sltiu;

						ParseRegister(oper1,&(Decode_inst[i].d));
						ParseRegister(oper2,&(Decode_inst[i].s1));
						Decode_inst[i].s2 = -1;
						Decode_inst[i].imm = abs(atoi(oper3));
						//printf("Op: %d %d %d %d\n", Decode_inst[i].op, Decode_inst[i].d, Decode_inst[i].s1, Decode_inst[i].imm);
					}
					else if((strcmp(opcode,"mult") == 0) || (strcmp(opcode, "div") == 0) || (strcmp(opcode, "divu") == 0))
					{
						if(strcmp(opcode, "mult") == 0)
							Decode_inst[i].op = mult;
						else if(strcmp(opcode, "div") == 0)
							Decode_inst[i].op = div;
						else if(strcmp(opcode, "divu") == 0)
							Decode_inst[i].op = divu;

						Decode_inst[i].d = HI_LO;
						ParseRegister(oper1, &(Decode_inst[i].s1));
						ParseRegister(oper2, &(Decode_inst[i].s2));
						Decode_inst[i].imm=-1;
						//printf("Op: %d %d %d %d\n", Decode_inst[i].op, Decode_inst[i].d, Decode_inst[i].s1, Decode_inst[i].s2);
					}
					else if((strcmp(opcode,"add.s") == 0) || (strcmp(opcode,"add.d") == 0) || (strcmp(opcode, "sub.s") == 0) || (strcmp(opcode, "sub.d") == 0) ||
						(strcmp(opcode, "mul.s") == 0) || (strcmp(opcode, "mul.d") == 0) || (strcmp(opcode, "div.d") == 0))
					{
						if(strcmp(opcode,"add.s") == 0)
							Decode_inst[i].op = adds;
						else if(strcmp(opcode,"add.d") == 0)
							Decode_inst[i].op = addd;
						else if(strcmp(opcode,"sub.s") == 0)
							Decode_inst[i].op = subs;
						else if(strcmp(opcode, "sub.d") == 0)
							Decode_inst[i].op = subd;
						else if(strcmp(opcode, "mul.s") == 0)
							Decode_inst[i].op = muls;
						else if(strcmp(opcode, "mul.d") == 0)
							Decode_inst[i].op = muld;
						else if(strcmp(opcode, "div.d") == 0)
							Decode_inst[i].op = divd;

						ParseRegister(oper1,&(Decode_inst[i].d));
						ParseRegister(oper2,&(Decode_inst[i].s1));
						ParseRegister(oper3,&(Decode_inst[i].s2));
						Decode_inst[i].imm = -1;
						//printf("Op: %d %d %d %d\n", Decode_inst[i].op, Decode_inst[i].d, Decode_inst[i].s1, Decode_inst[i].s2);
					}
					else if((strcmp(opcode,"mov.d") == 0) || (strcmp(opcode,"neg.d") == 0) || (strcmp(opcode,"cvt.s.d") == 0) ||
						(strcmp(opcode,"cvt.s.w") == 0) || (strcmp(opcode,"cvt.d.s") == 0) || (strcmp(opcode,"cvt.d.w") == 0) ||
						(strcmp(opcode,"cvt.w.d") == 0) || (strcmp(opcode,"sqrt.d") == 0) || (strcmp(opcode,"mfc1") == 0) ||
						(strcmp(opcode,"dmfc1") == 0) || (strcmp(opcode,"mtc1") == 0) || (strcmp(opcode,"dmtc1") == 0) ||
						(strcmp(opcode,"jalr") == 0))
					{
						if(strcmp(opcode,"mov.d") == 0)
							Decode_inst[i].op = movd;
						else if(strcmp(opcode,"neg.d") == 0)
							Decode_inst[i].op = negd;
						else if(strcmp(opcode,"cvt.s.d") == 0)
							Decode_inst[i].op = cvtsd;
						else if(strcmp(opcode,"cvt.s.w") == 0)
							Decode_inst[i].op = cvtsw;
						else if(strcmp(opcode,"cvt.d.s") == 0)
							Decode_inst[i].op = cvtds;
						else if(strcmp(opcode, "cvt.d.w") == 0)
							Decode_inst[i].op = cvtdw;
						else if(strcmp(opcode, "cvt.w.d") == 0)
							Decode_inst[i].op = cvtwd;
						else if(strcmp(opcode, "sqrt.d") == 0)
							Decode_inst[i].op = sqrtd;
						else if(strcmp(opcode, "mfc1") == 0)
							Decode_inst[i].op = mfc1;
						else if(strcmp(opcode, "dmfc1") == 0)
							Decode_inst[i].op = dmfc1;
						else if(strcmp(opcode, "mtc1") == 0)
							Decode_inst[i].op = mtc1;
						else if(strcmp(opcode, "dmtc1") == 0)
							Decode_inst[i].op = dmtc1;
						else if(strcmp(opcode, "jalr") == 0)
							Decode_inst[i].op = jalr;

						ParseRegister(oper1,&(Decode_inst[i].d));
						ParseRegister(oper2,&(Decode_inst[i].s1));
						Decode_inst[i].s2 = -1;
						Decode_inst[i].imm = -1;
						//printf("Op: %d %d %d\n", Decode_inst[i].op, Decode_inst[i].d, Decode_inst[i].s1);
					}
					else if((strcmp(opcode,"lb") == 0) || (strcmp(opcode,"lbu") == 0) || (strcmp(opcode,"lh") == 0) ||
						(strcmp(opcode,"lhu") == 0) || (strcmp(opcode,"lw") == 0) || (strcmp(opcode,"l.s") == 0) || (strcmp(opcode,"l.d") == 0))
					{
						if(strcmp(opcode,"lb") == 0)
							Decode_inst[i].op = lb;
							else if(strcmp(opcode,"lbu") == 0)
							Decode_inst[i].op = lbu;
						else if(strcmp(opcode,"lh") == 0)
							Decode_inst[i].op = lh;
						else if(strcmp(opcode,"lhu") == 0)
							Decode_inst[i].op = lhu;
						else if(strcmp(opcode,"lw") == 0)
							Decode_inst[i].op = lw;
						else if(strcmp(opcode,"l.s") == 0)
							Decode_inst[i].op = ls;
						else if(strcmp(opcode,"l.d") == 0)
							Decode_inst[i].op = ld;

						ParseRegister(oper1,&(Decode_inst[i].d));
						ParseAddress(oper2,&(Decode_inst[i].s1),&(Decode_inst[i].imm));
						Decode_inst[i].s2 = -1;
						//printf("Op: %d %d %d %d\n", Decode_inst[i].op, Decode_inst[i].d, Decode_inst[i].s1, Decode_inst[i].imm);
					}
					else if((strcmp(opcode,"sb") == 0) || (strcmp(opcode,"sh") == 0) || (strcmp(opcode,"sw") == 0) || (strcmp(opcode,"s.s") == 0) ||
						(strcmp(opcode,"s.d") == 0))
					{
						if(strcmp(opcode,"sb") == 0)
							Decode_inst[i].op = sb;
						else if(strcmp(opcode,"sh") == 0)
							Decode_inst[i].op = sh;
						else if(strcmp(opcode,"sw") == 0)
							Decode_inst[i].op = sw;
						else if(strcmp(opcode,"s.s") == 0)
							Decode_inst[i].op = ss;
						else if(strcmp(opcode,"s.d") == 0)
							Decode_inst[i].op = sd;

						ParseRegister(oper1,&(Decode_inst[i].s1));
						ParseAddress(oper2,&(Decode_inst[i].s2),&(Decode_inst[i].imm));
						Decode_inst[i].d = -1;
						//printf("Op: %d %d %d %d\n", Decode_inst[i].op, Decode_inst[i].s1, Decode_inst[i].s2, Decode_inst[i].imm);

					}
					else if((strcmp(opcode,"mfhi") == 0) || (strcmp(opcode,"mflo") == 0))
					{
						if(strcmp(opcode,"mfhi") == 0)
							Decode_inst[i].op = mfhi;
						else if(strcmp(opcode,"mflo") == 0)
							Decode_inst[i].op = mflo;

						Decode_inst[i].s2 = -1;
						Decode_inst[i].s1 = HI_LO;
						Decode_inst[i].imm = -1;
						ParseRegister(oper1,&(Decode_inst[i].d));
						//printf("Op: %d %d %d\n", Decode_inst[i].op, Decode_inst[i].d, Decode_inst[i].s1);
					}
					else if((strcmp(opcode,"lui") == 0))
					{
						Decode_inst[i].op = lui;
						Decode_inst[i].s1 = -1;
						Decode_inst[i].s2 = -1;
						ParseRegister(oper1,&(Decode_inst[i].d));
						Decode_inst[i].imm = atoi(oper2);
						//printf("Op: %d %d %d\n", Decode_inst[i].op, Decode_inst[i].d, Decode_inst[i].imm);
					}
					else if((strcmp(opcode,"c.eq.d") == 0) || (strcmp(opcode,"c.lt.d") == 0) || (strcmp(opcode,"c.le.d") == 0))
					{
						if(strcmp(opcode,"c.eq.d") == 0)
							Decode_inst[i].op = ceqd;
						else if(strcmp(opcode,"c.lt.d") == 0)
							Decode_inst[i].op = cltd;
						else if(strcmp(opcode,"c.le.d") == 0)
							Decode_inst[i].op = cled;

						Decode_inst[i].d = FCC;
						ParseRegister(oper1,&(Decode_inst[i].s1));
						ParseRegister(oper2,&(Decode_inst[i].s2));
						Decode_inst[i].imm = -1;
						//printf("Op: %d %d %d %d\n", Decode_inst[i].op, Decode_inst[i].d, Decode_inst[i].s1, Decode_inst[i].s2);
					}
					else if((strcmp(opcode,"beq") == 0) || (strcmp(opcode,"bne") == 0))
					{
						if(strcmp(opcode,"beq") == 0)
							Decode_inst[i].op = beq;
						else if(strcmp(opcode,"bne") == 0)
							Decode_inst[i].op = bne;

						Decode_inst[i].d = -1;
						ParseRegister(oper1,&(Decode_inst[i].s1));
						ParseRegister(oper2,&(Decode_inst[i].s2));
						Decode_inst[i].imm = atoi(oper3);
						//printf("Op: %d %d %d %d\n", Decode_inst[i].op, Decode_inst[i].s1, Decode_inst[i].s2, Decode_inst[i].imm);
					}
					else if((strcmp(opcode,"blez") == 0) || (strcmp(opcode,"bgtz") == 0) || (strcmp(opcode,"bltz") == 0) || (strcmp(opcode,"bgez") == 0))
					{
						if(strcmp(opcode,"blez") == 0)
							Decode_inst[i].op = blez;
						else if(strcmp(opcode,"bgtz") == 0)
							Decode_inst[i].op = bgtz;
						else if(strcmp(opcode,"bltz") == 0)
							Decode_inst[i].op = bltz;
						else if(strcmp(opcode,"bgez") == 0)
							Decode_inst[i].op = bgez;

						Decode_inst[i].d = -1;
						Decode_inst[i].s2 = -1;
						ParseRegister(oper1,&(Decode_inst[i].s1));
						Decode_inst[i].imm = atoi(oper2);
						//printf("Op: %d %d %d\n", Decode_inst[i].op, Decode_inst[i].s1, Decode_inst[i].imm);
					}
					else if((strcmp(opcode,"bc1f") == 0) || (strcmp(opcode,"bc1t") == 0))
					{
						if(strcmp(opcode,"bc1f") == 0)
							Decode_inst[i].op = bc1f;
						else if(strcmp(opcode,"bc1t") == 0)
							Decode_inst[i].op = bc1t;

						Decode_inst[i].d = -1;
						Decode_inst[i].s2 = -1;
						Decode_inst[i].s1 = FCC;
						Decode_inst[i].imm = atoi(oper1);
						//printf("Op: %d %d %d\n", Decode_inst[i].op, Decode_inst[i].s1, Decode_inst[i].imm);
					}
					else if((strcmp(opcode,"j") == 0) || (strcmp(opcode,"jal") == 0))
					{
						if(strcmp(opcode,"j") == 0)
							Decode_inst[i].op = j;
						else if(strcmp(opcode,"jal") == 0)
							Decode_inst[i].op = jal;

						Decode_inst[i].d = -1;
						Decode_inst[i].s1 = -1;
						Decode_inst[i].s2 = -1;
						Decode_inst[i].imm = atoi(oper1);
						//printf("Op: %d %d\n", Decode_inst[i].op, Decode_inst[i].imm);
					}
					else if((strcmp(opcode,"jr") == 0))
					{
						Decode_inst[i].op = jr;
						Decode_inst[i].d = -1;
						Decode_inst[i].s2 = -1;
						ParseRegister(oper1,&(Decode_inst[i].s1));
						Decode_inst[i].imm = -1;
						//printf("Op: %d %d\n", Decode_inst[i].op, Decode_inst[i].s1);
					}
				}
			}
		}
		ID.total_no_instr_fetched=IF.total_no_instr_fetched;

			for(i=0; i < ID.total_no_instr_fetched; i++)
			{
				if(IF_ID[i].valid==1)
				{

				if(((tail_dispatch+1)%512)==head_dispatch) // check if dispatch is full ?
				{
					//printf("ROB overflow - wait for instructions to finish\n");
					dispatch_overflow_stall = 1;
				}
				else
				{
					dispatch_overflow_stall = 0;
					if(head_dispatch== -1)
					{
						head_dispatch=tail_dispatch=0;
						goto nxt;
					}
					else                		// adding instructions into rob buffer
					{//x
						tail_dispatch=(tail_dispatch+1)%512;
						nxt:
						insert=tail_dispatch;
						available_dispatch=insert;
					}
					DISPATCH[available_dispatch].op = Decode_inst[i].op;
					DISPATCH[available_dispatch].d = Decode_inst[i].d;
					DISPATCH[available_dispatch].s1 = Decode_inst[i].s1;
					DISPATCH[available_dispatch].s2 = Decode_inst[i].s2;
					DISPATCH[available_dispatch].imm = Decode_inst[i].imm;
					DISPATCH[available_dispatch].PC = IF_ID[i].IR_buf.PC;
					DISPATCH[available_dispatch].valid = IF_ID[i].valid;
					DISPATCH[available_dispatch].busy = 1;
					DISPATCH[available_dispatch].fetch_time = IF_ID[i].IR_buf.fetch_time;
					DISPATCH[available_dispatch].branch_taken = IF_ID[i].branch_taken;
					DISPATCH[available_dispatch].branch_prediction = IF_ID[i].branch_prediction;
					IF_ID[i].valid = 0;
				}

			}
		}
	}
}
/*-------------------------------------------------------------------------------------------------------------*/
/************************************************Dispatch stage*************************************************/
void Dispatch()
{ //dispatch

	int jj;
	int ii;

	for(i=0; i < SW; i++)
	{//sw
		IR_inserted_flag=0;

		dis_valid = DISPATCH[head_dispatch].valid;
		if(dis_valid == 0)
		{
			// Do nothing stall
		}
		else
		{//zz2
			if (DISPATCH[head_dispatch].d !=(-1)) // these are the instruction which have output register in ARF .INT/FPP/LOG/LOAD/JALR
			{ 	//z2
			for (a=0;a<RRF_no;a++) // Check vacancy in RRF
				{ //z1
					if(IR_inserted_flag==1)
						break;

					if(RRF[a].busy==0)
					{ //z
						available_rrf=a;
						if(((tail_rob+1)%ROB_no)==head_rob) // check if rob is full ?
						{
							//printf("ROB overflow - wait for instructions to finish\n");
							rob_overflow_stall = 1;
						}
						else
						{ //y
							rob_overflow_stall = 0;
							if(head_rob== -1)             // adding instructions into rob buffer
							{
								head_rob=tail_rob=0;
								goto next;
							}
							else                		// adding instructions into rob buffer
							{//x
								tail_rob=(tail_rob+1)%ROB_no;
								next:
								b=tail_rob;
								available_rob=b;
						 		for(c=0;c<RS_entries;c++)
						 		  {//x5
       /*INT RS*/	 			   if((DISPATCH[head_dispatch].d>=r0)&&(DISPATCH[head_dispatch].d<=r30)&&(DISPATCH[head_dispatch].op!=lb)&&(DISPATCH[head_dispatch].op!=lbu)&&(DISPATCH[head_dispatch].op!=lh)&&(DISPATCH[head_dispatch].op!=lhu)&&(DISPATCH[head_dispatch].op!=lw)&&(DISPATCH[head_dispatch].op!=ls)&&(DISPATCH[head_dispatch].op!=ld))// to check integer registers
						 			   {//x1
						 				   if(RS_int[c].busy==0)
						 					{//RSINT
						 					   available_rs_int=c;
						    // SOURCE READ
						 					   src_value1=DISPATCH[head_dispatch].s1;
						 					   src_value2=DISPATCH[head_dispatch].s2;
						 					   src_imm=DISPATCH[head_dispatch].imm;
						 					  if(ARF[src_value1].reg_dst==0)
						 					   ARF[src_value1].reg_dst=DISPATCH[head_dispatch].s1;

						 					   if(DISPATCH[head_dispatch].s1==ARF[src_value1].reg_dst)
						 					   {
						 						  RS_int[c].operand1=DISPATCH[head_dispatch].s1;
												  RS_int[c].d = DISPATCH[head_dispatch].d;
												  RS_int[c].op = DISPATCH[head_dispatch].op;
												  RS_int[c].PC = DISPATCH[head_dispatch].PC;
												  RS_int[c].fetch_time = DISPATCH[head_dispatch].fetch_time;
												  RS_int[c].busy = 1;
						 						  if(ARF[src_value1].busy==0)
						 						    RS_int[c].valid1=1;
						 						  else
						 						  {
													RS_int[c].valid1 = 0;
													RS_int[c].operand1 = ARF[src_value1].tag;

						 						  }
						 					   }

						 					   if(ARF[src_value2].reg_dst==0)
						 					   ARF[src_value2].reg_dst= DISPATCH[head_dispatch].s2;

						 					   if(DISPATCH[head_dispatch].s2==ARF[src_value2].reg_dst)
						 					  {
						 					  	RS_int[c].operand2=DISPATCH[head_dispatch].s2;
						 					  	if(ARF[src_value2].busy==0)
						 					  		RS_int[c].valid2=1;
						 					  	else
						 					  	{
													RS_int[c].valid2 = 0;
													RS_int[c].operand2 = ARF[src_value2].tag;

						 					  	}
						 					  }
											 if(DISPATCH[head_dispatch].s1 == r0)
											 {
												  RS_int[c].operand1=DISPATCH[head_dispatch].s1;
												  RS_int[c].d = DISPATCH[head_dispatch].d;
												  RS_int[c].op = DISPATCH[head_dispatch].op;
												  RS_int[c].PC = DISPATCH[head_dispatch].PC;
												  RS_int[c].fetch_time = DISPATCH[head_dispatch].fetch_time;
												  RS_int[c].busy = 1;
												  RS_int[c].valid1 = 1;
											 }
						 					 if(DISPATCH[head_dispatch].imm && DISPATCH[head_dispatch].s2 < 0)
						 					 {
						 						 RS_int[c].operand2=DISPATCH[head_dispatch].imm;
						 						 RS_int[c].valid2=1;
						 					 }

				//DEstination allocate
						 					RRF[available_rrf].busy=1;
						 					index_to_arf= available_rrf;
						 					RRF[available_rrf].reg_dst=DISPATCH[head_dispatch].d;
						 					RRF[available_rrf].valid=0;
						 					ROB[available_rob].busy=1;
						 					ROB[available_rob].issued=1;
						 					ROB[available_rob].PC= DISPATCH[head_dispatch].PC;
											ROB[available_rob].fetch_time=DISPATCH[head_dispatch].fetch_time;
						 					ROB[available_rob].finished=0;
											ROB[available_rob].d=RS_int[c].d;
											ROB[available_rob].rrf_tag = available_rrf;
						 					RS_int[available_rs_int].ROB_tag=available_rob;
						 					if(DISPATCH[head_dispatch].d==ARF[DISPATCH[head_dispatch].d].reg_dst)
						 					{
						 						ARF[DISPATCH[head_dispatch].d].busy=1;
						 						ARF[DISPATCH[head_dispatch].d].tag= index_to_arf;
						 						ARF[DISPATCH[head_dispatch].d].reg_dst=DISPATCH[head_dispatch].d;

						 					}
											DISPATCH[head_dispatch].busy = 0;
											dispatch_overflow_stall = 0;
											if(head_dispatch == tail_dispatch)
												head_dispatch = tail_dispatch = -1;
											else
												head_dispatch=(head_dispatch+1)%512;

						 					IR_inserted_flag=1;
						 				}//RSINT
						 				   if(IR_inserted_flag==1)
						 				   	break;
										   else if(IR_inserted_flag == 0 && c == RS_entries-1)
											tail_rob=(tail_rob-1)%ROB_no;
						 			}//x1
       	   	   	   	   	   	   	   if(IR_inserted_flag==1)
       	   	   	   	   	   	   		   break;
       	   	   	   	   	   	   	   //continue

/*Fpp RS */							 else if((DISPATCH[head_dispatch].d>=f0)&&(DISPATCH[head_dispatch].d<=FCC)&&(DISPATCH[head_dispatch].op!=lb)&&(DISPATCH[head_dispatch].op!=lbu)&&(DISPATCH[head_dispatch].op!=lh)&&(DISPATCH[head_dispatch].op!=lhu)&&(DISPATCH[head_dispatch].op!=lw)&&(DISPATCH[head_dispatch].op!=ls)&&(DISPATCH[head_dispatch].op!=ld))
						 				 {// x2
						 					 if(RS_fpp[c].busy==0)
						 					 {//rsfpp
						 						 available_rs_fpp=c;
							 // SOURCE READ
						 						 src_value1=DISPATCH[head_dispatch].s1;
						 						 src_value2=DISPATCH[head_dispatch].s2;
						 						 src_imm=DISPATCH[head_dispatch].imm;
						 						 if(ARF[src_value1].reg_dst==0)
						 							 ARF[src_value1].reg_dst=DISPATCH[head_dispatch].s1;
						 						 if(ARF[src_value2].reg_dst==0)
						 							 ARF[src_value2].reg_dst=DISPATCH[head_dispatch].s2;

						 						 if(DISPATCH[head_dispatch].s1==ARF[src_value1].reg_dst)
						 						 {
						 							 RS_fpp[c].operand1=DISPATCH[head_dispatch].s1;
												 	 RS_fpp[c].d = DISPATCH[head_dispatch].d;
												  	 RS_fpp[c].op = DISPATCH[head_dispatch].op;
												  	 RS_fpp[c].PC = DISPATCH[head_dispatch].PC;
													 RS_fpp[c].fetch_time = DISPATCH[head_dispatch].fetch_time;
												  	 RS_fpp[c].busy = 1;
						 							 if(ARF[src_value1].busy==0)
						 							 	 RS_fpp[c].valid1=1;
						 							 else
						 							 {
														RS_fpp[c].valid1 = 0;
														RS_fpp[c].operand1 = ARF[src_value1].tag;

						 							 }
						 						 }
						 						 if(DISPATCH[head_dispatch].s2==ARF[src_value2].reg_dst)
						 						 {
						 							 RS_fpp[c].operand2=DISPATCH[head_dispatch].s2;
						 							 if(ARF[src_value2].busy==0)
						 							 	 RS_fpp[c].valid2=1;
						 							 else
						 							 {
														RS_fpp[c].valid2 = 0;
														RS_fpp[c].operand2 = ARF[src_value2].tag;

						 							 }
						 						 }
												 if(DISPATCH[head_dispatch].s1 == r0)
											 	 {
												  	RS_fpp[c].operand1=DISPATCH[head_dispatch].s1;
												  	RS_fpp[c].d = DISPATCH[head_dispatch].d;
												  	RS_fpp[c].op = DISPATCH[head_dispatch].op;
												  	RS_fpp[c].PC = DISPATCH[head_dispatch].PC;
												  	RS_fpp[c].fetch_time = DISPATCH[head_dispatch].fetch_time;
												  	RS_fpp[c].busy = 1;
												  	RS_fpp[c].valid1 = 1;
											 	 }
												 if(DISPATCH[head_dispatch].s2 == r0)
												 {
													RS_fpp[c].operand2=0;
													RS_fpp[c].valid2=1;
												 }
						 						 if(DISPATCH[head_dispatch].imm && DISPATCH[head_dispatch].s2 < 0)
						 						 {
						 							 RS_fpp[c].operand2=DISPATCH[head_dispatch].imm;
						 							 RS_fpp[c].valid2=1;
						 						 }

						//DEstination allocate
						 						 RRF[available_rrf].busy=1;
						 						 index_to_arf= available_rrf;
						 						 RRF[available_rrf].reg_dst=DISPATCH[head_dispatch].d;
						 						 RRF[available_rrf].valid=0;
						 						 ROB[available_rob].busy=1;
						 						 ROB[available_rob].issued=1;
						 						 ROB[available_rob].PC= DISPATCH[head_dispatch].PC;
												 ROB[available_rob].fetch_time = DISPATCH[head_dispatch].fetch_time;
						 						 ROB[available_rob].finished=0;
												 ROB[available_rob].rrf_tag = available_rrf;
						 						 RS_fpp[available_rs_fpp].ROB_tag=available_rob;
						 						 if(DISPATCH[head_dispatch].d==ARF[DISPATCH[head_dispatch].d].reg_dst)
						 						 {
						 							 ARF[DISPATCH[head_dispatch].d].busy=1;
						 							 ARF[DISPATCH[head_dispatch].d].tag= index_to_arf;
						 							 ARF[DISPATCH[head_dispatch].d].reg_dst=DISPATCH[head_dispatch].d;
						 						 }
												DISPATCH[head_dispatch].busy = 0;
												dispatch_overflow_stall = 0;
												if(head_dispatch == tail_dispatch)
													head_dispatch = tail_dispatch = -1;
												else
													head_dispatch=(head_dispatch+1)%512;
						 						 IR_inserted_flag=1;
						 					 }//rsfpp
						 					if(IR_inserted_flag==1)
						 						break;
											else if(IR_inserted_flag == 0 && c == RS_entries-1)
												tail_rob=(tail_rob-1)%ROB_no;
						 				 }// x2

/*for Load inst, RS mem */			else if((DISPATCH[head_dispatch].op==lb)||(DISPATCH[head_dispatch].op==lbu)||(DISPATCH[head_dispatch].op==lh)||(DISPATCH[head_dispatch].op==lhu)||(DISPATCH[head_dispatch].op==lw)||(DISPATCH[head_dispatch].op==ls)||(DISPATCH[head_dispatch].op==ld))  //branch instructions
						 				{//x3
											if(((tail_rs_mem +1)%RS_entries)==head_rs_mem)
											{
												//printf("overflow");
												tail_rob=(tail_rob-1)%ROB_no;
												rs_mem_overflow_stall = 1;
												break;
											}
											else
											{//mem3
												rs_mem_overflow_stall = 0;
												if(head_rs_mem==-1)
												{
													head_rs_mem=tail_rs_mem=0;
													goto nxt3;
												}
												else
												{//mem2
													tail_rs_mem=(tail_rs_mem+1)%RS_entries;
													nxt3:
													c=tail_rs_mem;
													available_rs_mem= c;

						 					 if(RS_mem[c].busy==0)
						 					 {//rsmem
						 						 available_rs_mem=c;
						 // SOURCE READ
						 						 src_value1=DISPATCH[head_dispatch].s1;
						 						 src_value2=DISPATCH[head_dispatch].s2;
						 						 src_imm=DISPATCH[head_dispatch].imm;
						 						 if(ARF[src_value1].reg_dst==0)
						 							 ARF[src_value1].reg_dst=DISPATCH[head_dispatch].s1;
						 						 if(ARF[src_value2].reg_dst==0)
						 							 ARF[src_value2].reg_dst=DISPATCH[head_dispatch].s2;

						 						 if(DISPATCH[head_dispatch].s1==ARF[src_value1].reg_dst)
						 						 {
						 							 RS_mem[c].operand1=DISPATCH[head_dispatch].s1;
												 	 RS_mem[c].d = DISPATCH[head_dispatch].d;
												  	 RS_mem[c].op = DISPATCH[head_dispatch].op;
												  	 RS_mem[c].PC = DISPATCH[head_dispatch].PC;
													 RS_mem[c].fetch_time = DISPATCH[head_dispatch].fetch_time;
												  	 RS_mem[c].busy = 1;
						 							 if(ARF[src_value1].busy==0)
						 								 RS_mem[c].valid1=1;
						 							 else
						 							 {
														RS_mem[c].valid1 = 0;
														RS_mem[c].operand1 = ARF[src_value1].tag;

						 							 }
						 						 }
						 						 if(DISPATCH[head_dispatch].s2==ARF[src_value2].reg_dst && src_value2 != -1)
						 						 {
						 							 RS_mem[c].operand2=DISPATCH[head_dispatch].s2;
						 							 if(ARF[src_value2].busy==0)
						 								 RS_mem[c].valid2=1;
						 							 else
						 							 {
														RS_mem[c].valid2 = 0;
														RS_mem[c].operand2 = ARF[src_value2].tag;

						 							 }
						 						 }
						 						 if(DISPATCH[head_dispatch].imm || DISPATCH[head_dispatch].imm==0)
						 						 {
						 							 RS_mem[c].operand2=DISPATCH[head_dispatch].imm;
						 							 RS_mem[c].valid2=1;
						 						 }

						//DEstination allocate
						 						 RRF[available_rrf].busy=1;
						 						 index_to_arf= available_rrf;
						 						 RRF[available_rrf].reg_dst=DISPATCH[head_dispatch].d;
						 						 RRF[available_rrf].valid=0;
						 						 ROB[available_rob].busy=1;
						 						 ROB[available_rob].issued=1;
						 						 ROB[available_rob].PC= DISPATCH[head_dispatch].PC;
												 ROB[available_rob].fetch_time = DISPATCH[head_dispatch].fetch_time;
						 						 ROB[available_rob].finished=0;
												 ROB[available_rob].rrf_tag = available_rrf;
						 						 RS_mem[available_rs_mem].ROB_tag=available_rob;
						 						 if(DISPATCH[head_dispatch].d==ARF[DISPATCH[head_dispatch].d].reg_dst)
						 						 {
						 							 ARF[DISPATCH[head_dispatch].d].busy=1;
						 							 ARF[DISPATCH[head_dispatch].d].tag= index_to_arf;
						 							 ARF[DISPATCH[head_dispatch].d].reg_dst=DISPATCH[head_dispatch].d;

						 						 }
												DISPATCH[head_dispatch].busy = 0;
												dispatch_overflow_stall = 0;
												if(head_dispatch == tail_dispatch)
													head_dispatch = tail_dispatch = -1;
												else
													 head_dispatch=(head_dispatch+1)%512; // tail not being updated
						 						 IR_inserted_flag=1;
						 					 }//rsmem
						 					 if(IR_inserted_flag==1)
						 						 break;
											 else if(IR_inserted_flag == 0 && c == RS_entries-1)
												tail_rob=(tail_rob-1)%ROB_no;
												}
											    }

						 					}//x3

/*for jalr Rs br	*/			else if(DISPATCH[head_dispatch].op==jalr)
									{ //x4

				 						if(RS_br[c].busy==0)
				 						{//rsbr
				/*source read*/ 				available_rs_br=c;
						 				src_value1=DISPATCH[head_dispatch].s1;
						 				src_value2=DISPATCH[head_dispatch].s2;
						 				src_imm=DISPATCH[head_dispatch].imm;
						 				if(ARF[src_value1].reg_dst==0)
						 					ARF[src_value1].reg_dst=DISPATCH[head_dispatch].s1;
						 				if(ARF[src_value2].reg_dst==0)
						 					ARF[src_value2].reg_dst=DISPATCH[head_dispatch].s2;
						 				if(DISPATCH[head_dispatch].s1==ARF[src_value1].reg_dst)
						 				{
						 					RS_br[c].operand1=DISPATCH[head_dispatch].s1;
											RS_br[c].op = DISPATCH[head_dispatch].op;
											RS_br[c].PC = DISPATCH[head_dispatch].PC;
										  	RS_br[c].fetch_time = DISPATCH[head_dispatch].fetch_time;
											RS_br[c].d = DISPATCH[head_dispatch].d;
											RS_br[c].busy = 1;
						 					if(ARF[src_value1].busy==0)
						 						RS_br[c].valid1=1;
						 					else
						 					{
												RS_br[c].valid1 = 0;
												RS_br[c].operand1 = ARF[src_value1].tag;

						 					}
						 				}
						 				if(DISPATCH[head_dispatch].s2==ARF[src_value2].reg_dst && src_value2 != -1)
						 				{
						 					RS_br[c].operand2=DISPATCH[head_dispatch].s2;
						 					if(ARF[src_value2].busy==0)
						 						RS_br[c].valid2=1;
						 					else
						 					{
												RS_br[c].valid2 = 0;
												RS_br[c].operand2 = ARF[src_value2].tag;

						 					}
						 				}


	//DEstination is not allocated in RRF AND ARF
										RS_br[c].valid2 = 1;
										RS_br[c].operand2 = -1;
						 				RRF[available_rrf].busy=1;
						 				index_to_arf= available_rrf;
						 				RRF[available_rrf].reg_dst=DISPATCH[head_dispatch].d;
						 				RRF[available_rrf].valid=0;
						 				ROB[available_rob].busy=1;
						 				ROB[available_rob].issued=1;
						 				ROB[available_rob].PC= DISPATCH[head_dispatch].PC;
										ROB[available_rob].fetch_time = DISPATCH[head_dispatch].fetch_time;
						 				ROB[available_rob].finished=0;
										ROB[available_rob].rrf_tag = available_rrf;
										RS_br[available_rs_br].branch_prediction = DISPATCH[head_dispatch].branch_prediction;
										RS_br[available_rs_br].branch_taken = DISPATCH[head_dispatch].branch_taken;
						 				RS_br[available_rs_br].ROB_tag=available_rob;
						 				if(DISPATCH[head_dispatch].d==ARF[DISPATCH[head_dispatch].d].reg_dst)
						 				{
						 					ARF[DISPATCH[head_dispatch].d].busy=1;
						 					ARF[DISPATCH[head_dispatch].d].tag= index_to_arf;
						 					ARF[DISPATCH[head_dispatch].d].reg_dst=DISPATCH[head_dispatch].d;

						 				}
										DISPATCH[head_dispatch].busy = 0;
										dispatch_overflow_stall = 0;
										if(head_dispatch == tail_dispatch)
											head_dispatch = tail_dispatch = -1;
										else
											head_dispatch=(head_dispatch+1)%512;
						 				IR_inserted_flag=1;
				 						}//rsbr
				 						if(IR_inserted_flag==1)
				 							break;
										else if(IR_inserted_flag == 0 && c == RS_entries-1)
											tail_rob=(tail_rob-1)%ROB_no;
									}//x4
						 		  }//x5
						 		}//closing x
							}// y
						 }// z
					}// z1
				//break;
				}// z2
      /* -------------------------------------------------------------------------------------------------*/
			else if(DISPATCH[head_dispatch].d ==(-1)) //zz1
			{
/*Jump/br inst .. RS_BR*/
				if(DISPATCH[head_dispatch].op == nop || DISPATCH[head_dispatch].op == syscall)
				{
					if(((tail_rob+1)%ROB_no)==head_rob)
					{
						rob_overflow_stall = 1;
					}
					else
					{
						rob_overflow_stall = 0;
						if(head_rob == -1)
						{
							head_rob=tail_rob=0;
							goto nxt5;
						}
						else
						{
							tail_rob = (tail_rob+1)%ROB_no;
							nxt5:
							b = tail_rob;
							available_rob=b;
							ROB[available_rob].busy = 1;
							ROB[available_rob].issued = 1;
							ROB[available_rob].PC = DISPATCH[head_dispatch].PC;
							ROB[available_rob].fetch_time = DISPATCH[head_dispatch].fetch_time;
							ROB[available_rob].finished = 1;
							DISPATCH[head_dispatch].busy = 0;
							dispatch_overflow_stall = 0;
							if(head_dispatch == tail_dispatch)
								head_dispatch = tail_dispatch = -1;
							else
								head_dispatch=(head_dispatch+1)%512;
							IR_inserted_flag= 1;
							if(IR_inserted_flag==1)
								break;
						}
					}
				}
				if((DISPATCH[head_dispatch].op == j)||(DISPATCH[head_dispatch].op == jal)||(DISPATCH[head_dispatch].op == jr)||(DISPATCH[head_dispatch].op == beq)||(DISPATCH[head_dispatch].op == bne)||(DISPATCH[head_dispatch].op == blez)||(DISPATCH[head_dispatch].op == bgtz)||(DISPATCH[head_dispatch].op == bltz)||(DISPATCH[head_dispatch].op == bgez) ||(DISPATCH[head_dispatch].op == bc1f)||(DISPATCH[head_dispatch].op == bc1t))
				{//br5
					if(((tail_rob+1)%ROB_no)==head_rob) // check if rob is full ?
					{
						//printf("ROB overflow - wait for instructions to finish\n");
						rob_overflow_stall = 1;
					}
					else
						{//br4
							rob_overflow_stall = 0;
							if(head_rob== -1) // adding instructions into rob buffer
							{
								head_rob=tail_rob=0;
								goto next1;
							}
							else                // adding instructions into rob buffer //x
							{//br3
								tail_rob=(tail_rob+1)%ROB_no;
								next1:
								b=tail_rob;
								available_rob=b;
						 		for(c=0;c<RS_entries;c++)
						 		  {//br2
									if(RS_br[c].busy==0)
									{//br1
										available_rs_br=c;
										src_value1=DISPATCH[head_dispatch].s1;
										src_value2=DISPATCH[head_dispatch].s2;
										src_imm=DISPATCH[head_dispatch].imm;
										if(ARF[src_value1].reg_dst==0)
											ARF[src_value1].reg_dst=DISPATCH[head_dispatch].s1;
										if(ARF[src_value2].reg_dst==0)
											ARF[src_value2].reg_dst=DISPATCH[head_dispatch].s2;
										if(DISPATCH[head_dispatch].s1==ARF[src_value1].reg_dst)
										{
											RS_br[c].operand1=DISPATCH[head_dispatch].s1;
											RS_br[c].op = DISPATCH[head_dispatch].op;
											RS_br[c].PC = DISPATCH[head_dispatch].PC;
										  	RS_br[c].fetch_time = DISPATCH[head_dispatch].fetch_time;
											RS_br[c].d = DISPATCH[head_dispatch].d;
											RS_br[c].busy = 1;
											if(ARF[src_value1].busy==0)
												RS_br[c].valid1=1;
											else
											{
												RS_br[c].valid1 = 0;
												RS_br[c].operand1 = ARF[src_value1].tag;

											}
										}
										if(DISPATCH[head_dispatch].s2==ARF[src_value2].reg_dst)
										{
											RS_br[c].operand2=DISPATCH[head_dispatch].s2;
											if(ARF[src_value2].busy==0)
												RS_br[c].valid2=1;
											else
											{
												RS_br[c].valid2 = 0;
												RS_br[c].operand2 = ARF[src_value2].tag;

											}
										}
										if(DISPATCH[head_dispatch].s1 == r0)
										{
											RS_br[c].operand1=0;
											RS_br[c].valid1 = 1;
										}
										if(DISPATCH[head_dispatch].s2 == r0)
										{
											RS_br[c].operand2=0;
											RS_br[c].valid2 = 1;
										}
										if(DISPATCH[head_dispatch].imm && DISPATCH[head_dispatch].op == jal)
										{
											RS_br[c].operand1=DISPATCH[head_dispatch].imm;
											RS_br[c].valid2=1;
											RS_br[c].valid1=1;
										}
										else if(DISPATCH[head_dispatch].imm && DISPATCH[head_dispatch].op == blez)
										{
											RS_br[c].operand2 = DISPATCH[head_dispatch].imm;
											RS_br[c].valid2 = 1;
										}

	//DEstination is not allocated in RRF AND ARF
										ROB[available_rob].busy=1;
										ROB[available_rob].issued=1;
										ROB[available_rob].PC= DISPATCH[head_dispatch].PC;
										ROB[available_rob].fetch_time = DISPATCH[head_dispatch].fetch_time;
										ROB[available_rob].finished=0;
										RS_br[available_rs_br].branch_prediction = DISPATCH[head_dispatch].branch_prediction;
										RS_br[available_rs_br].branch_taken = DISPATCH[head_dispatch].branch_taken;
										RS_br[available_rs_br].ROB_tag=available_rob;
										DISPATCH[head_dispatch].busy = 0;
										dispatch_overflow_stall = 0;
										if(head_dispatch == tail_dispatch)
											head_dispatch = tail_dispatch = -1;
										else
											head_dispatch=(head_dispatch+1)%512;
										IR_inserted_flag= 1;
										if(IR_inserted_flag==1)
											break;
									}//br1
								  if(IR_inserted_flag == 0 && c == RS_entries-1)
									tail_rob=(tail_rob-1)%ROB_no;
						 		  }//br2
							}//br3
						}//br4
				}//br5
/*SW instruc RS MEM*/
			else if((DISPATCH[head_dispatch].op == sb)||(DISPATCH[head_dispatch].op == sh)||(DISPATCH[head_dispatch].op == sw)||(DISPATCH[head_dispatch].op == ss)||(DISPATCH[head_dispatch].op == sd))
				{//mem6
					if(((tail_rob+1)%ROB_no)==head_rob) // check if rob is full ?
					{
						//printf("ROB overflow - wait for instructions to finish\n");
						rob_overflow_stall = 1;
					}
					else
					{//mem5
						rob_overflow_stall = 0;
						if(head_rob== -1) // adding instructions into rob buffer
						{
							head_rob=tail_rob=0;
							goto next2;
						}
						else                // adding instructions into rob buffer //x
						{//mem4
							tail_rob=(tail_rob+1)%ROB_no;
							next2:
							b=tail_rob;
							available_rob=b;
							if(((tail_rs_mem +1)%RS_entries)==head_rs_mem)
							{
								//printf("overflow");
								tail_rob = (tail_rob-1)%ROB_no;
								rs_mem_overflow_stall = 1;
							}
							else
							{//mem3
								rs_mem_overflow_stall = 0;
								if(head_rs_mem==-1)
								{
									head_rs_mem=tail_rs_mem=0;
									goto next3;
								}
								else
								{//mem2
									tail_rs_mem=(tail_rs_mem+1)%RS_entries;
									next3:
									c=tail_rs_mem;
									available_rs_mem= c;
									if(RS_mem[c].busy==0)
									{//mem1

			/*SOURCE READ*/			src_value1=DISPATCH[head_dispatch].s1;
			                        src_value2=DISPATCH[head_dispatch].s2;
			                        src_imm=DISPATCH[head_dispatch].imm;
			                        if(ARF[src_value1].reg_dst==0)
			                        	ARF[src_value1].reg_dst=DISPATCH[head_dispatch].s1;
			                        if(ARF[src_value2].reg_dst==0)
			                        	ARF[src_value2].reg_dst=DISPATCH[head_dispatch].s2;
			                        if(DISPATCH[head_dispatch].s1==ARF[src_value1].reg_dst)
			                        {
			                        	RS_mem[c].operand1=DISPATCH[head_dispatch].s1;
							RS_mem[c].op = DISPATCH[head_dispatch].op;
							RS_mem[c].PC = DISPATCH[head_dispatch].PC;
							RS_mem[c].fetch_time = DISPATCH[head_dispatch].fetch_time;
							RS_mem[c].d = DISPATCH[head_dispatch].d;
							RS_mem[c].busy = 1;
			                        	if(ARF[src_value1].busy==0)
			                        		RS_mem[c].valid1=1;
			                        	else
			                        	{
								RS_mem[c].valid1 = 0;
								RS_mem[c].operand1 = ARF[src_value1].tag;

			                        	}
			                        }
			                        if(DISPATCH[head_dispatch].s2==ARF[src_value2].reg_dst)
			                        {
			                        	RS_mem[c].operand2=DISPATCH[head_dispatch].s2;
			                        	if(ARF[src_value2].busy==0)
			                        		RS_mem[c].valid2=1;
			                        	else
			                        	{
								RS_mem[c].valid2 = 0;
								RS_mem[c].operand2 = ARF[src_value2].tag;

			                        	}
			                        }
						if(DISPATCH[head_dispatch].s1 == r0)
						{
							RS_mem[c].operand1=DISPATCH[head_dispatch].s1;
							RS_mem[c].op = DISPATCH[head_dispatch].op;
							RS_mem[c].PC = DISPATCH[head_dispatch].PC;
							RS_mem[c].fetch_time = DISPATCH[head_dispatch].fetch_time;
							RS_mem[c].d = DISPATCH[head_dispatch].d;
							RS_mem[c].busy = 1;
							RS_mem[c].operand1=0;
							RS_mem[c].valid1 = 1;
						}


			                        //DEstination is not allocated in RRF AND ARF

						ROB[available_rob].busy=1;
						ROB[available_rob].issued=1;
						ROB[available_rob].PC= DISPATCH[head_dispatch].PC;
						ROB[available_rob].fetch_time = DISPATCH[head_dispatch].fetch_time;
						ROB[available_rob].finished=0;
						RS_mem[available_rs_mem].ROB_tag=available_rob;
						DISPATCH[head_dispatch].busy = 0;
						dispatch_overflow_stall = 0;
						if(head_dispatch == tail_dispatch)
							head_dispatch = tail_dispatch = -1;
						else
							head_dispatch=(head_dispatch+1)%512;
						IR_inserted_flag=1;
						if(IR_inserted_flag==1)
							//break;      /* change 1*/
							continue;
									}//mem1
							}//mem2
						}//mem3
					}//mem4
			   }//mem5
		 }//mem6
		}//zz1
		}//zz2
	}//sw

	DIS.total_no_instr_fetched=ID.total_no_instr_fetched;

	for(i=0; i < DIS.total_no_instr_fetched; i++)
	{

		DIS_ISS[i].valid = 1;

	}

}

/*---------------------------------------------------------------------------------------------------------*/
/**********************************Issue stage***********************************************************/
void Issue()
{

	int jj;
	int index;
	int earliest_inst = -1;
	int insert = 0;
	iss_valid = DIS_ISS[0].valid;
	if(iss_valid == 0)
	{
		// Do nothing - stall
	}
	else
	{
		//Mark any instructions as Ready
		for(jj=0; jj<RS_entries;jj++)
		{
			if(RS_int[jj].busy == 1)
			{
				if((RS_int[jj].valid1 == 1 && RS_int[jj].valid2 == 1) || (RS_int[jj].valid1 == 1 && RRF[ARF[RS_int[jj].operand2].tag].valid == 1) || (RS_int[jj].valid2 == 1 && RRF[ARF[RS_int[jj].operand1].tag].valid == 1) || (RRF[ARF[RS_int[jj].operand1].tag].valid == 1 && RRF[ARF[RS_int[jj].operand2].tag].valid == 1))
				RS_int[jj].ready = 1;
			}
			if(RS_fpp[jj].busy == 1)
			{
				if((RS_fpp[jj].valid1 == 1 && RS_fpp[jj].valid2 == 1) || (RS_fpp[jj].valid1 == 1 && RRF[ARF[RS_fpp[jj].operand2].tag].valid == 1) || (RS_fpp[jj].valid2 == 1 && RRF[ARF[RS_fpp[jj].operand1].tag].valid == 1) || (RRF[ARF[RS_fpp[jj].operand1].tag].valid == 1 && RRF[ARF[RS_fpp[jj].operand2].tag].valid == 1))
				RS_fpp[jj].ready = 1;
			}
			if(RS_mem[jj].busy == 1)
			{
				if((RS_mem[jj].valid1 == 1 && RS_mem[jj].valid2 == 1) || (RS_mem[jj].operand2 < 32 && RS_mem[jj].valid1 == 1 && RRF[ARF[RS_mem[jj].operand2].tag].valid == 1) || (RS_mem[jj].operand1 < 32 && RS_mem[jj].valid2 == 1 && RRF[ARF[RS_mem[jj].operand1].tag].valid == 1) || (RS_mem[jj].operand1 < 32 && RS_mem[jj].operand2 < 32 && RRF[ARF[RS_mem[jj].operand1].tag].valid == 1 && RRF[ARF[RS_mem[jj].operand2].tag].valid == 1))
				RS_mem[jj].ready = 1;
			}
			if(RS_br[jj].busy == 1)
			{
				if((RS_br[jj].valid1 == 1 && RS_br[jj].valid2 == 1) || (RS_br[jj].valid1 == 1 && RRF[ARF[RS_br[jj].operand2].tag].valid == 1) || (RS_br[jj].valid2 == 1 && RRF[ARF[RS_br[jj].operand1].tag].valid == 1) || (RRF[ARF[RS_br[jj].operand1].tag].valid == 1 && RRF[ARF[RS_br[jj].operand2].tag].valid == 1))
				RS_br[jj].ready = 1;
			}
		}
		//Issue Instructions to Integer FU
		for(jj=0; jj<FU_no; jj++)
		{
			if(FU_int[jj].busy == 0)
			{
				for(index=0; index<RS_entries; index++)
				{
					if(RS_int[index].busy == 1 && RS_int[index].ready == 1)
					{
						if(earliest_inst == -1)
						{
							earliest_inst = RS_int[index].fetch_time;
							insert = index;
						}
						else if(RS_int[index].fetch_time < earliest_inst)
						{
							earliest_inst = RS_int[index].fetch_time;
							insert = index;
						}
					}
				}

				if(RS_int[insert].busy == 1 && RS_int[insert].ready == 1)
				{
					//Send to FU
					FU_int[jj].d = RS_int[insert].d;
					FU_int[jj].operand1 = RS_int[insert].operand1;
					FU_int[jj].operand2 = RS_int[insert].operand2;
					FU_int[jj].op = RS_int[insert].op;
					FU_int[jj].ROB_tag = RS_int[insert].ROB_tag;
					FU_int[jj].busy = 1;
					RS_int[insert].busy = 0;
					RS_int[insert].valid1 = 0;
					RS_int[insert].valid2 = 0;
				}
			}
		}
		earliest_inst = -1;
		//Issue Instructions to Floating Point FU
		for(jj=0; jj<FU_no; jj++)
		{
			if(FU_fpp[jj].busy == 0)
			{
				for(index=0; index<RS_entries; index++)
				{
					if(RS_fpp[index].busy == 1 && RS_fpp[index].ready == 1)
					{
						if(earliest_inst == -1)
						{
							earliest_inst = RS_fpp[index].fetch_time;
							insert = index;
						}
						else if(RS_fpp[index].fetch_time < earliest_inst)
						{
							earliest_inst = RS_fpp[index].fetch_time;
							insert = index;
						}
					}
				}
				if(RS_fpp[insert].busy == 1 && RS_fpp[insert].ready == 1)
				{
					//Send to FU
					FU_fpp[jj].d = RS_fpp[insert].d;
					FU_fpp[jj].operand1 = RS_fpp[insert].operand1;
					FU_fpp[jj].operand2 = RS_fpp[insert].operand2;
					FU_fpp[jj].op = RS_fpp[insert].op;
					FU_fpp[jj].ROB_tag = RS_fpp[insert].ROB_tag;
					FU_fpp[jj].busy = 1;
					RS_fpp[insert].busy = 0;
					RS_fpp[insert].valid1 = 0;
					RS_fpp[insert].valid2 = 0;
				}
			}
		}
		//Issue Instructions to  Memory FU
		for(jj=0; jj<FU_no; jj++)
		{
			if(FU_mem[jj].busy == 0)
			{
				if(RS_mem[head_rs_mem].busy == 1 && RS_mem[head_rs_mem].ready == 1)
				{
					if(L1_data_miss!=1)
					{
						if(((rand()%100)<= L1_data_hitrate)&& (L1_data_miss==0))
						{// Generating a random number for the L1 data cache
							FU_mem[jj].memory_execute_time = 2+L1_data_time;
						}
						else
						{
							L1_data_miss=1;
							continue;
						}
					}
					if((L1_data_miss==1)&&(rand()%100<=L2_hitrate))
					{ // Generating a random number for L2 cache
						FU_mem[jj].memory_execute_time = 2+L1_data_time+L2_time;
						L1_data_miss = 0;
						continue;
					}
					else if(L1_data_miss==1)
					{
						FU_mem[jj].memory_execute_time = 2+L1_data_time+L2_time+MEM_time;
						L2_data_miss=1;
						continue;
					}
					if(L2_data_miss==1)
					{
		    				L1_data_miss=0;
		    				L2_data_miss=0;
					}

					//Send to FU
					FU_mem[jj].d = RS_mem[head_rs_mem].d;
					FU_mem[jj].operand1 = RS_mem[head_rs_mem].operand1;
					FU_mem[jj].operand2 = RS_mem[head_rs_mem].operand2;
					FU_mem[jj].op = RS_mem[head_rs_mem].op;
					FU_mem[jj].ROB_tag = RS_mem[head_rs_mem].ROB_tag;
					FU_mem[jj].busy = 1;
					RS_mem[head_rs_mem].busy = 0;
					RS_mem[head_rs_mem].valid1 = 0;
					RS_mem[head_rs_mem].valid2 = 0;
					if(head_rs_mem == tail_rs_mem)
						head_rs_mem = tail_rs_mem = -1;
					else
						head_rs_mem=(head_rs_mem+1)%RS_entries;
				}
			}
		}
		//Issue Instructions to Branch FU
		earliest_inst = -1;
		for(jj=0; jj<1; jj++)
		{
			if(FU_br[jj].busy == 0)
			{
				for(index=0; index<RS_entries; index++)
				{
					if(RS_br[index].busy == 1 && RS_br[index].ready == 1)
					{
						if(earliest_inst == -1)
						{
							earliest_inst = RS_br[index].fetch_time;
							insert = index;
						}
						else if(RS_br[index].fetch_time < earliest_inst)
						{
							earliest_inst = RS_br[index].fetch_time;
							insert = index;
						}
					}
				}
				if(RS_br[insert].busy == 1 && RS_br[insert].ready == 1)
				{
					//Send to FU
					FU_br[jj].d = RS_br[insert].d;
					FU_br[jj].operand1 = RS_br[insert].operand1;
					FU_br[jj].operand2 = RS_br[insert].operand2;
					FU_br[jj].op = RS_br[insert].op;
					FU_br[jj].ROB_tag = RS_br[insert].ROB_tag;
					FU_br[jj].busy = 1;
					FU_br[jj].branch_prediction = RS_br[insert].branch_prediction;
					FU_br[jj].branch_taken = RS_br[insert].branch_taken;
					RS_br[insert].busy = 0;
					RS_br[insert].valid1 = 0;
					RS_br[insert].valid2 = 0;
				}
			}
		}
	}

for(i=0; i < SW; i++)
{
	ISS_EX[i].valid = DIS_ISS[i].valid;
}
}


/*-----------------------------------------------------------------------------------------------------------*/
/*********************************************Execute stage ****************************************************/
void Execute()
{
	int gshare_index;
	int cc;
	ex_valid = ISS_EX[0].valid;
	if(ex_valid == 0)
	{
		//Do nothing stall
	}
	else
	{
		//Execute Instructions in Integer Functional Unit
		for(i=0; i<FU_no; i++)
		{
			if(FU_int[i].busy == 1)
				FU_int[i].execute_cycles += 1;
			if(FU_int[i].busy == 1)
			{
				if(FU_int[i].op == addi || FU_int[i].op == add || FU_int[i].op == subi || FU_int[i].op == sub || FU_int[i].op == addu ||
				FU_int[i].op == addiu || FU_int[i].op == subu || FU_int[i].op == and || FU_int[i].op == andi || FU_int[i].op == or ||
				FU_int[i].op == ori || FU_int[i].op == xor || FU_int[i].op == xori || FU_int[i].op == nor || FU_int[i].op == sll ||
				FU_int[i].op == sllv || FU_int[i].op == srl || FU_int[i].op == srlv || FU_int[i].op == sra || FU_int[i].op == srav ||
				FU_int[i].op == slt || FU_int[i].op == slti || FU_int[i].op == sltu || FU_int[i].op == sltiu)
				{
					//Integer Add/Sub 1 Cycle Latency
					FU_int[i].busy = 0;
					ROB[FU_int[i].ROB_tag].finished = 1;
					//update data in RRF
					RRF[ARF[FU_int[i].d].tag].valid = 1;
					FU_int[i].execute_cycles = 0;

				}
				else
				{
					//Integer Multiply/Divide 3 Cyle Latency
					if(FU_int[i].execute_cycles == 3)
					{
						FU_int[i].busy = 0;
						ROB[FU_int[i].ROB_tag].finished = 1;
						FU_int[i].execute_cycles = 0;
						//update data in RRF
						RRF[ARF[FU_int[i].d].tag].valid = 1;
					}
				}
			}
		}
		//Execute Instructions in Floating Point Functional Unit 5 Cycle Latency
		for(i=0; i<FU_no; i++)
		{
			if(FU_fpp[i].busy == 1)
				FU_fpp[i].execute_cycles += 1;
			if(FU_fpp[i].execute_cycles == 5)
			{
				FU_fpp[i].busy = 0;
				ROB[FU_fpp[i].ROB_tag].finished = 1;
				FU_fpp[i].execute_cycles = 0;
				//update data in RRF
				RRF[ARF[FU_fpp[i].d].tag].valid = 1;
			}
		}
		//Execute Instructions in Memory Functional Unit 2 Cycle Latency
		for(i=0; i<FU_no; i++)
		{
			if(FU_mem[i].busy == 1)
				FU_mem[i].execute_cycles += 1;
			//check if hit or miss and add to total cycles
			if(FU_mem[i].execute_cycles == FU_mem[i].memory_execute_time && FU_mem[i].busy==1)
			{
				FU_mem[i].busy = 0;
				ROB[FU_mem[i].ROB_tag].finished = 1;
				FU_mem[i].execute_cycles = 0;
				//update data in RRF
			}
		}
		//Execute Instructions in Branch Functional Unit 1 Cycle Latency
		if(FU_br[0].busy == 1)
			FU_br[0].execute_cycles += 1;
		if(FU_br[0].execute_cycles == 1)
		{
			if(FU_br[0].op == jalr)
				RRF[ARF[FU_br[i].d].tag].valid = 1;
			FU_br[0].busy = 0;
			ROB[FU_br[0].ROB_tag].finished = 1;
			FU_br[0].execute_cycles = 0;
			if(BTB_tail == -1)
				BTB_tail = 0;
			for(cc=0; cc<BTB_tail; cc++)
			{
				if(BTB[cc] == ROB[FU_br[0].ROB_tag].PC)
					break;
			}
			if(BTB[cc] == ROB[FU_br[0].ROB_tag].PC)
			{
				gshare_index = ((ROB[FU_br[0].ROB_tag].PC&0x3FF)>>3) ^ bhsr;
			}
			else
			{
				BTB[BTB_tail] = ROB[FU_br[0].ROB_tag].PC;
				gshare_index = ((BTB[BTB_tail]&0x3FF) >> 3) ^ bhsr;
			}
			if(gshare[gshare_index] == 0)
			{
				if(FU_br[0].branch_taken == 1)
					gshare[gshare_index] = 1;
			}
			else if(gshare[gshare_index] == 1)
			{
				if(FU_br[0].branch_taken == 1)
					gshare[gshare_index] = 2;
				else
					gshare[gshare_index] = 0;
			}
			else if(gshare[gshare_index] == 2)
			{
				if(FU_br[0].branch_taken == 1)
					gshare[gshare_index] = 3;
				else
					gshare[gshare_index] = 1;
			}
			else if(gshare[gshare_index] == 3)
			{
				if(FU_br[0].branch_taken == 0)
					gshare[gshare_index] = 2;
			}
			if(FU_br[0].branch_taken == 0)
				bhsr = ((bhsr << 1) | 0) & 0x3FF;
			if(FU_br[0].branch_taken == 1)
				bhsr = ((bhsr << 1) | 1) & 0x3FF;
			BTB_tail += 1;
			if(BTB_tail > BTB_size)
				BTB_tail = 0;
		}

	}
	for(i=0; i < SW; i++)
	{
		EX_COM[i].valid = ISS_EX[i].valid;
	}
}


/*-------------------------------------------------------------------------------------------------------------*/
/*******************************Commit stage ***************************************/
void Commit()
{
	int jj;
	for(i=0; i < SW; i++)
	{
		com_valid = EX_COM[i].valid;
		if(com_valid == 0)
		{
			// Do nothing stall
		}
		else
		{
			if(ROB[head_rob].finished == 1)
			{
				//printf("Finished Instruction at %d %d\n", ROB[head_rob].PC, ROB[head_rob].fetch_time);
				ROB[head_rob].busy = 0;
				ROB[head_rob].finished = 0;
				ROB[head_rob].issued = 0;
				ROB[head_rob].valid = 0;
				if(ROB[head_rob].d != -1)
				{
					/*
					RRF[ARF[ROB[head_rob].d].tag].busy = 0;
					RRF[ARF[ROB[head_rob].d].tag].valid = 0;
					RRF[ARF[ROB[head_rob].d].tag].reg_dst = 0;*/
					RRF[ROB[head_rob].rrf_tag].busy = 0;
					RRF[ROB[head_rob].rrf_tag].valid = 0;
					RRF[ROB[head_rob].rrf_tag].reg_dst = 0;
				}
				for(jj=0; jj<RS_entries; jj++)
				{
					if(RS_int[jj].valid1 == 0 && RS_int[jj].operand1 == ROB[head_rob].rrf_tag && RS_int[jj].busy == 1)
						RS_int[jj].valid1 = 1;
					if(RS_int[jj].valid2 == 0 && RS_int[jj].operand2 == ROB[head_rob].rrf_tag && RS_int[jj].busy == 1)
						RS_int[jj].valid2 = 1;
					if(RS_fpp[jj].valid1 == 0 && RS_int[jj].operand1 == ROB[head_rob].rrf_tag && RS_fpp[jj].busy == 1)
						RS_fpp[jj].valid1 = 1;
					if(RS_fpp[jj].valid2 == 0 && RS_fpp[jj].operand2 == ROB[head_rob].rrf_tag && RS_fpp[jj].busy == 1)
						RS_fpp[jj].valid2 = 1;
					if(RS_mem[jj].valid1 == 0 && RS_mem[jj].operand1 == ROB[head_rob].rrf_tag && RS_mem[jj].busy == 1)
						RS_mem[jj].valid1 = 1;
					if(RS_mem[jj].valid2 == 0 && RS_mem[jj].operand2 == ROB[head_rob].rrf_tag && RS_mem[jj].busy == 1)
						RS_mem[jj].valid2 = 1;
					if(RS_br[jj].valid1 == 0 && RS_br[jj].operand1 == ROB[head_rob].rrf_tag && RS_br[jj].busy == 1)
						RS_br[jj].valid1 = 1;
					if(RS_br[jj].valid2 == 0 && RS_br[jj].operand2 == ROB[head_rob].rrf_tag && RS_br[jj].busy == 1)
						RS_br[jj].valid2 = 1;

				}
				if(ROB[head_rob].rrf_tag == ARF[ROB[head_rob].d].tag)
				{
					ARF[ROB[head_rob].d].reg_dst = 0;
					ARF[ROB[head_rob].d].busy = 0;
				}
				if(head_rob == tail_rob)
					head_rob = tail_rob = -1;
				else
					head_rob=(head_rob+1)%ROB_no;
				finished_instructions = finished_instructions + 1;
			}
		}
	}
}

void ParseLineIntoTokens(char *line,		/* input */
                         char *parse_chars,	/* token separators */
                         char **field1,		/* output; may be NULL */
                         char **field2,		/* output; may be NULL */
                         char **field3)		/* output; may be NULL */

{
	char	*field4,input[80];

	//strcpy(input,line);	/* only used for error reporting */
	*field1=strtok(line,parse_chars);
	if (*field1 != NULL)
  		*field2=strtok(NULL,parse_chars);
	else
  		*field2=NULL;

	if (*field2 != NULL)
		*field3=strtok(NULL,parse_chars);
	else
  		*field3=NULL;

	if (*field3 != NULL)
		field4=strtok(NULL,parse_chars);
	else
		field4=NULL;

	if (field4 != NULL)
	{
  		printf("Too many fields in the following line or operand field:\n");
  		printf("%s",input);
  		exit(0);
  	}
}

void ParseRegister(char	*operand,	/* input */
                    int *reg_tag)	/* output */

{
	if (strcmp(operand,"r0") == 0) *reg_tag=r0;
	else if (strcmp(operand,"r1") == 0) *reg_tag=r1;
	else if (strcmp(operand,"r2") == 0) *reg_tag=r2;
	else if (strcmp(operand,"r3") == 0) *reg_tag=r3;
	else if (strcmp(operand,"r4") == 0) *reg_tag=r4;
	else if (strcmp(operand,"r5") == 0) *reg_tag=r5;
	else if (strcmp(operand,"r6") == 0) *reg_tag=r6;
	else if (strcmp(operand,"r7") == 0) *reg_tag=r7;
	else if (strcmp(operand,"r8") == 0) *reg_tag=r8;
	else if (strcmp(operand,"r9") == 0) *reg_tag=r9;
	else if (strcmp(operand,"r10") == 0) *reg_tag=r10;
	else if (strcmp(operand,"r11") == 0) *reg_tag=r11;
	else if (strcmp(operand,"r12") == 0) *reg_tag=r12;
	else if (strcmp(operand,"r13") == 0) *reg_tag=r13;
	else if (strcmp(operand,"r14") == 0) *reg_tag=r14;
	else if (strcmp(operand,"r15") == 0) *reg_tag=r15;
	else if (strcmp(operand,"r16") == 0) *reg_tag=r16;
	else if (strcmp(operand,"r17") == 0) *reg_tag=r17;
	else if (strcmp(operand,"r18") == 0) *reg_tag=r18;
	else if (strcmp(operand,"r19") == 0) *reg_tag=r19;
	else if (strcmp(operand,"r20") == 0) *reg_tag=r20;
	else if (strcmp(operand,"r21") == 0) *reg_tag=r21;
	else if (strcmp(operand,"r22") == 0) *reg_tag=r22;
	else if (strcmp(operand,"r23") == 0) *reg_tag=r23;
	else if (strcmp(operand,"r24") == 0) *reg_tag=r24;
	else if (strcmp(operand,"r25") == 0) *reg_tag=r25;
	else if (strcmp(operand,"r26") == 0) *reg_tag=r26;
	else if (strcmp(operand,"r27") == 0) *reg_tag=r27;
	else if (strcmp(operand,"r28") == 0) *reg_tag=r28;
	else if (strcmp(operand,"r29") == 0) *reg_tag=r29;
	else if (strcmp(operand,"r30") == 0) *reg_tag=r30;
	else if (strcmp(operand,"r31") == 0) *reg_tag=r31;
	else if (strcmp(operand,"f0") == 0) *reg_tag=f0;
	else if (strcmp(operand,"f1") == 0) *reg_tag=f1;
	else if (strcmp(operand,"f2") == 0) *reg_tag=f2;
	else if (strcmp(operand,"f3") == 0) *reg_tag=f3;
	else if (strcmp(operand,"f4") == 0) *reg_tag=f4;
	else if (strcmp(operand,"f5") == 0) *reg_tag=f5;
	else if (strcmp(operand,"f6") == 0) *reg_tag=f6;
	else if (strcmp(operand,"f7") == 0) *reg_tag=f7;
	else if (strcmp(operand,"f8") == 0) *reg_tag=f8;
	else if (strcmp(operand,"f9") == 0) *reg_tag=f9;
	else if (strcmp(operand,"f10") == 0) *reg_tag=f10;
	else if (strcmp(operand,"f11") == 0) *reg_tag=f11;
	else if (strcmp(operand,"f12") == 0) *reg_tag=f12;
	else if (strcmp(operand,"f13") == 0) *reg_tag=f13;
	else if (strcmp(operand,"f14") == 0) *reg_tag=f14;
	else if (strcmp(operand,"f15") == 0) *reg_tag=f15;
	else if (strcmp(operand,"f16") == 0) *reg_tag=f16;
	else if (strcmp(operand,"f17") == 0) *reg_tag=f17;
	else if (strcmp(operand,"f18") == 0) *reg_tag=f18;
	else if (strcmp(operand,"f19") == 0) *reg_tag=f19;
	else if (strcmp(operand,"f20") == 0) *reg_tag=f20;
	else if (strcmp(operand,"f21") == 0) *reg_tag=f21;
	else if (strcmp(operand,"f22") == 0) *reg_tag=f22;
	else if (strcmp(operand,"f23") == 0) *reg_tag=f23;
	else if (strcmp(operand,"f24") == 0) *reg_tag=f24;
	else if (strcmp(operand,"f25") == 0) *reg_tag=f25;
	else if (strcmp(operand,"f26") == 0) *reg_tag=f26;
	else if (strcmp(operand,"f27") == 0) *reg_tag=f27;
	else if (strcmp(operand,"f28") == 0) *reg_tag=f28;
	else if (strcmp(operand,"f29") == 0) *reg_tag=f29;
	else if (strcmp(operand,"f30") == 0) *reg_tag=f30;
	else if (strcmp(operand,"HI_LO") == 0) *reg_tag=HI_LO;
	else if (strcmp(operand,"FCC") == 0) *reg_tag=FCC;
	else
	{
  		printf("Unrecognizable register field:\n%s\n",operand);
  	exit(0);
  	}
}

void ParseAddress(char *operand,	/* input */
                   int *reg_tag,	/* output */
                   int *value)		/* output */

{
	int	i;
	char	reg_string[80],immed_string[80];

	i=0;
	while (i < strlen(operand)  &&  ((i == 0  &&  operand[i] == '-')  || (operand[i] >= '0'  &&  operand[i] <= '9')))
  		i++;
	if (i == 0  ||  i == strlen(operand)  ||  (i == 1  &&  operand[0] == '-'))
  	{
  		printf("Unrecognizable address field:\n%s\n",operand);
  		exit(0);
  	}
	strcpy(reg_string,&(operand[i]));
	strcpy(immed_string,operand);
	immed_string[i]='\0';
	*value=atoi(immed_string);
	if (reg_string[0] != '('  ||  reg_string[strlen(reg_string)-1] != ')')
  	{
  		printf("Unrecognizable address field:\n%s\n",operand);
  		exit(0);
  	}
	reg_string[strlen(reg_string)-1]='\0';
	ParseRegister(&(reg_string[1]),reg_tag);
}

void ParseImmediate(char *operand,	/* input */
                    int *value)		/* output */

{
  	*value=atoi(operand);
}
