
module Control_Unit(
    output reg Load_NPC,
    output reg Load_PC,
    output reg Load_IR,
    output reg Load_RegA,
    output reg Load_RegB,
    output reg Load_Imm,
    output reg WT_Reg,
	 output reg [3 : 0] Addr_Reg,
    output reg [2 : 0] Extend,
    output reg [7 : 0] Send_Reg,
    output reg Load_LMD,
    output reg Cond_Kind,
	 output reg [1 : 0] Jump_Kind,
    output reg Sel_Mux1,
    output reg Sel_Mux2,
    output reg [1 : 0] Sel_Mux4,
    output reg [4 : 0] Cal_ALU,
    output reg Write,
    output reg Load_ALU,
    input clk,
    input [15 : 0] IR_in,
    input rst,
	 output reg [2 : 0] state,
	 output reg [5 : 0] cur_ins
    );
	 
	reg [2 : 0] next_state;

	parameter
		ADDIU = 1,
		ADDIU3 = 2,
		ADDSP3 = 3,
		ADDSP = 4,
		ADDU = 5,
		AND = 6,
		B = 7,
		BEQZ = 8,
		BNEZ = 9,
		BTEQZ = 10,
		BTNEZ = 11,
		CMP = 12,
		CMPI = 13,
		INT = 14,
		JALR = 15,
		JR = 16,
		JRRA = 17,
		LI = 18,
		LW = 19,
		LW_SP = 20,
		MFIH = 21,
		MFPC = 22,
		MOVE = 23,
		MTIH = 24,
		MTSP = 25,
		NEG = 26,
		NOT = 27,
		NOP = 28,
		OR = 29,
		SLL = 30,
		SLLV = 31,
		SLT = 32,
		SLTI = 33,
		SLTU = 34,
		SLTUI = 35,
		SRA = 36,
		SRAV = 37,
		SRL = 38,
		SRLV = 39,
		SUBU = 40,
		SW = 41,
		SW_RS = 42,
		SW_SP = 43,
		XOR = 44,
		HLT = 45;

	parameter
		_Idle = 0,
		_IFetch = 1,
		_IDec = 2,
		_Exec = 3,
		_Mem = 4,
		_WB = 5,
		_Halt = 6;
		
	always @(IR_in or rst)		begin
		if (rst == 0)
		begin
			cur_ins = 0;
		end
		else
		begin
			case (IR_in[15 : 11])
				5'b01001:	cur_ins = ADDIU;
				5'b01000:	cur_ins = ADDIU3;
				5'b00000:	cur_ins = ADDSP3;
				5'b00010:	cur_ins = B;
				5'b00100:	cur_ins = BEQZ;
				5'b00101:	cur_ins = BNEZ;
				5'b01110:	cur_ins = CMPI;
				5'b11111:	cur_ins = INT;
				5'b01101:	cur_ins = LI;
				5'b10011:	cur_ins = LW;
				5'b10010:	cur_ins = LW_SP;
				5'b01111:	cur_ins = MOVE;
				5'b00001:	cur_ins = NOP;
				5'b01010:	cur_ins = SLTI;
				5'b01011:	cur_ins = SLTUI;
				5'b11011:	cur_ins = SW;
				5'b11010:	cur_ins = SW_SP;
				5'b10000:	cur_ins = HLT;
				5'b00110:	case (IR_in[1 : 0])
									2'b00:	cur_ins = SLL;
									2'b11:	cur_ins = SRA;
									2'b10:	cur_ins = SRL;
								endcase
				5'b01100:	case (IR_in[10 : 8])
									3'b011:	cur_ins = ADDSP;
									3'b000:	cur_ins = BTEQZ;
									3'b001:	cur_ins = BTNEZ;
									3'b100:	cur_ins = MTSP;
									3'b010:	cur_ins = SW_RS;
								endcase
				5'b11100:	case (IR_in[1 : 0])
									2'b01:	cur_ins = ADDU;
									2'b11:	cur_ins = SUBU;
								endcase
				5'b11101:	case (IR_in[4 : 0])
									5'b01100:	cur_ins = AND;
									5'b01010:	cur_ins = CMP;
									5'b01011:	cur_ins = NEG;
									5'b01111:	cur_ins = NOT;
									5'b01101:	cur_ins = OR;
									5'b00100:	cur_ins = SLLV;
									5'b00010:	cur_ins = SLT;
									5'b00011:	cur_ins = SLTU;
									5'b00111:	cur_ins = SRAV;
									5'b00110:	cur_ins = SRLV;
									5'b01110:	cur_ins = XOR;
									5'b00000:	case (IR_in[7 : 5])
														3'b110:	cur_ins = JALR;
														3'b000:	cur_ins = JR;
														3'b001:	cur_ins = JRRA;
														3'b010:	cur_ins = MFPC;
													endcase
								endcase
				5'b11110:	case (IR_in[7 : 0])
									8'b00000000:	cur_ins = MFIH;
									8'b00000001:	cur_ins = MTIH;
								endcase
			endcase
		end
	end

	always @(posedge clk or negedge rst)
	begin
		if (rst == 0)
		begin
			state <= _Idle;
		end
		else
		begin
			state <= next_state;
		end
	end

	always @(state)
	begin
		case (state)
			_Idle:
				begin
					Load_NPC = 0;
					Load_PC = 0;
					Load_IR = 0;
					Load_RegA = 0;
					Load_RegB = 0;
					Load_Imm = 0;
					WT_Reg = 0;
					Addr_Reg = 4'b0;
					Extend = 3'b0;
					Send_Reg = 8'b0;
					Load_LMD = 0;
					Cond_Kind = 0;
					Jump_Kind = 2'b0;
					Sel_Mux1 = 0;
					Sel_Mux2 = 0;
					Sel_Mux4 = 2'b0;
					Cal_ALU = 5'b0;
					Write = 0;
					Load_ALU = 0;
					next_state = _IFetch;
				end
				
			_IFetch:
				begin
					Write = 0;
					Load_LMD = 0;
					WT_Reg = 0;
					Load_PC = 0;
					
					next_state = _IDec;
					Load_IR = 1;
					Load_NPC = 1;
				end
			
			_IDec:
				begin
					Load_IR = 0;
					Load_NPC = 0;
					
					if (cur_ins == HLT)
					begin
						next_state = _Halt;
					end
					else
					begin
						next_state = _Exec;
					end
					
					case (cur_ins)
						ADDIU,
						ADDIU3,
						BEQZ,
						BNEZ,
						CMPI,
						JALR,
						JR,
						LW,
						MTIH,
						SLTI,
						SLTUI:	Send_Reg = {1'b0, IR_in[10 : 8], 4'b0};
						
						MOVE,
						MTSP,
						NOT,
						SLL,
						SRA,
						SRL:		Send_Reg = {1'b0, IR_in[7 : 5], 4'b0};
							
						ADDSP3,
						ADDSP,
						LW_SP:	Send_Reg = 8'b11110000;
						
						ADDU,
						AND,
						CMP,
						OR,
						SLLV,
						SLT,
						SLTU,
						SRAV,
						SRLV,
						SUBU,
						SW,
						XOR:		Send_Reg = {1'b0, IR_in[10 : 8], 1'b0, IR_in[7 : 5]};
						
						B,
						INT,
						LI,
						MFPC,
						NOP:		Send_Reg = 8'b00000000;
						
						JRRA:		Send_Reg = 8'b00100000;
						
						MFIH:		Send_Reg = 8'b11010000;
						
						NEG:		Send_Reg = {4'b0000, 1'b0, IR_in[7 : 5]};
						
						SW_RS:	Send_Reg = 8'b11110010;
						
						SW_SP:	Send_Reg = {4'b1111, 1'b0, IR_in[7 : 5]};
						
						BTEQZ,
						BTNEZ:	Send_Reg = 8'b11100000;
					endcase
					
					case (cur_ins)
						ADDIU,
						ADDSP3,
						ADDSP,
						BEQZ,
						BNEZ,
						BTEQZ,
						BTNEZ,
						CMPI,
						LW_SP,
						SLTI,
						SLTUI,
						SW_RS,
						SW_SP:	Extend = 0;
						
						ADDIU3:	Extend = 1;
						
						B:			Extend = 2;
						
						INT:		Extend = 3;
						
						LI:		Extend = 4;
						
						LW,
						SW:		Extend = 5;
						
						SLL,
						SRA,
						SRL:		Extend = 6;
					endcase
					
					case (cur_ins)
						ADDIU,
						ADDIU3,
						ADDSP3,
						ADDSP,
						ADDU,
						AND,
						CMP,
						CMPI,
						JALR,
						JR,
						JRRA,
						LW,
						LW_SP,
						MFIH,
						MOVE,
						MTIH,
						MTSP,
						NEG,
						NOT,
						OR,
						SLL,
						SLLV,
						SLT,
						SLTI,
						SLTU,
						SLTUI,
						SRA,
						SRAV,
						SRL,
						SRLV,
						SUBU,
						SW,
						SW_RS,
						SW_SP,
						XOR:		Sel_Mux1 = 0;
						
						B,
						BEQZ,
						BNEZ,
						BTEQZ,
						BTNEZ,
						MFPC:		Sel_Mux1 = 1;
					endcase
				
					case (cur_ins)
						ADDU,
						AND,
						CMP,
						NEG,
						OR,
						SLLV,
						SLT,
						SLTU,
						SRAV,
						SRLV,
						SUBU,
						XOR:		Sel_Mux2 = 0;
						
						ADDIU,
						ADDIU3,
						ADDSP3,
						ADDSP,
						B,
						BEQZ,
						BNEZ,
						BTEQZ,
						BTNEZ,
						CMPI,
						INT,
						LI,
						LW,
						LW_SP,
						SLL,
						SLTI,
						SLTUI,
						SRA,
						SRL,
						SW,
						SW_RS,
						SW_SP:	Sel_Mux2 = 1;
					endcase
					
					case (cur_ins)
						JALR,
						JR,
						JRRA,
						MFIH,
						MFPC,
						MOVE,
						MTIH,
						MTSP:		Cal_ALU = 0;
						
						INT,
						LI:		Cal_ALU = 1;
						
						ADDIU,
						ADDIU3,
						ADDSP3,
						ADDSP,
						ADDU,
						B,
						BEQZ,
						BNEZ,
						BTEQZ,
						BTNEZ,
						LW,
						LW_SP,
						SW,
						SW_RS,
						SW_SP:	Cal_ALU = 2;
						
						NEG,
						SUBU:		Cal_ALU = 3;

						AND:		Cal_ALU = 4;

						OR:		Cal_ALU = 5;

						NOT:		Cal_ALU = 6;

						XOR:		Cal_ALU = 7;

						CMP,
						CMPI:		Cal_ALU = 8;

						SLLV:		Cal_ALU = 9;

						SRLV:		Cal_ALU = 10;

						SLL:		Cal_ALU = 11;

						SLTU,
						SLTUI:	Cal_ALU = 12;

						SRAV:		Cal_ALU = 13;

						SRL:		Cal_ALU = 14;

						SRA:		Cal_ALU = 15;

						SLT,
						SLTI:		Cal_ALU = 16;
					endcase
				
					case (cur_ins)
						BEQZ,
						BTEQZ:	Cond_Kind = 0;
						
						BNEZ,
						BTNEZ:	Cond_Kind = 1;
					endcase
					
					case (cur_ins)
						BEQZ,
						BNEZ,
						BTEQZ,
						BTNEZ:	Jump_Kind = 2'b10;
						
						B,
						INT,
						JALR,
						JR,
						JRRA:		Jump_Kind = 2'b11;
						
						default:	Jump_Kind = 2'b00;
					endcase
					
					Load_RegA = 1;
					Load_RegB = 1;
					Load_Imm = 1;
				end
			
			_Exec:
				begin
					Load_RegA = 0;
					Load_RegB = 0;
					Load_Imm = 0;
					
					next_state = _Mem;
					
					Load_ALU = 1;
				end
			
			_Mem:
				begin
					Load_ALU = 0;
					
					case (cur_ins)
						B,
						BEQZ,
						BNEZ,
						BTEQZ,
						BTNEZ,
						SW,
						SW_RS,
						SW_SP,
						JR,
						JRRA:	next_state = _IFetch;
						
						default:	next_state = _WB;
					endcase
					
					case (cur_ins)
						SW,
						SW_RS,
						SW_SP:	Write = 1;
					endcase
					
					case (cur_ins)
						LW,
						LW_SP:	Load_LMD = 1;
					endcase
					
					Load_PC = 1;
					
					case (cur_ins)
						LW,
						LW_SP:	Sel_Mux4 = 1;
							
						INT,
						JALR:		Sel_Mux4 = 2;
						
						default:	Sel_Mux4 = 0;
					endcase
					
					case (cur_ins)
						ADDIU,
						ADDSP3,
						AND,
						LI,
						LW_SP,
						MFIH,
						MFPC,
						MOVE,
						NEG,
						NOT,
						OR,
						SLL,
						SRA,
						SRL,
						XOR:		Addr_Reg = {1'b0, IR_in[10 : 8]};

						ADDIU3,
						LW,
						SLLV,
						SRAV,
						SRLV:		Addr_Reg = {1'b0, IR_in[7 : 5]};

						ADDSP,
						MTSP:		Addr_Reg = 4'b1111;

						ADDU,
						SUBU:		Addr_Reg = {1'b0, IR_in[4 : 2]};

						CMP,
						CMPI,
						SLT,
						SLTI,
						SLTU,
						SLTUI:	Addr_Reg = 4'b1110;

						INT,
						JALR:		Addr_Reg = 4'b0010;

						MTIH:		Addr_Reg = 4'b1101;
					endcase
				end
			
			_WB:		begin
					Write = 0;
					Load_LMD = 0;
					Load_PC = 0;
					
					next_state = _IFetch;
					
					case (cur_ins)
						ADDIU,
						ADDSP3,
						AND,
						LI,
						LW_SP,
						MFIH,
						MFPC,
						MOVE,
						NEG,
						NOT,
						OR,
						SLL,
						SRA,
						SRL,
						XOR,
						ADDIU3,
						LW,
						SLLV,
						SRAV,
						SRLV,
						ADDSP,
						MTSP,
						ADDU,
						SUBU,
						CMP,
						CMPI,
						SLT,
						SLTI,
						SLTU,
						SLTUI,
						INT,
						JALR,
						MTIH:		WT_Reg = 1;
					endcase
				end
				
			_Halt:
				begin
					next_state = _Halt;
				end
		endcase
	end

endmodule
