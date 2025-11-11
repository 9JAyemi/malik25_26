// SVA checker for Control. Bind this to the DUT.
// Uses ##0 to avoid race with combinational updates.
module Control_sva
#(parameter Op_lw   = 6'b100011,
            Op_sw   = 6'b101011,
            Op_beq  = 6'b000100,
            Op_ALU  = 6'b000000,
            Op_j    = 6'b000010,
            Op_addi = 6'b001000)
(
  input  logic [5:0] Op_i,
  input  logic       RegDst_o, Jump_o, Branch_o, MemRead_o, MemtoReg_o, MemWrite_o, ALUSrc_o, RegWrite_o,
  input  logic [1:0] ALUOp_o
);

  localparam logic [5:0] Op_jal = 6'b000011;

  // Golden decode checks (bit-accurate to DUT)
  assert property (@(Op_i) ##0 RegDst_o   == ((Op_i==6'b0) || ((Op_i & 6'b111110)==6'b000010) || ((Op_i & 6'b111100)==6'b010000)));
  assert property (@(Op_i) ##0 Jump_o     == (Op_i==Op_j));
  assert property (@(Op_i) ##0 Branch_o   == (Op_i==Op_beq));
  assert property (@(Op_i) ##0 MemRead_o  == (Op_i==Op_lw));
  assert property (@(Op_i) ##0 MemtoReg_o == (Op_i==Op_lw));
  assert property (@(Op_i) ##0 ALUOp_o    == ((Op_i==Op_beq) ? 2'b01 :
                                              ((Op_i==Op_lw) || (Op_i==Op_sw) || (Op_i==Op_addi)) ? 2'b00 : 2'b10));
  assert property (@(Op_i) ##0 MemWrite_o == (Op_i==Op_sw));
  assert property (@(Op_i) ##0 ALUSrc_o   == ~((Op_i==Op_beq) || (Op_i==6'b0) || ((Op_i & 6'b111110)==6'b000010) || ((Op_i & 6'b111100)==6'b010000)));
  assert property (@(Op_i) ##0 RegWrite_o == ((Op_i==Op_lw) || (Op_i==Op_ALU) || (Op_i==Op_addi)));

  // Consistency/orthogonality invariants
  assert property (@(Op_i) ##0 !(MemRead_o && MemWrite_o));
  assert property (@(Op_i) ##0 (MemtoReg_o -> MemRead_o));
  assert property (@(Op_i) ##0 (RegWrite_o -> !MemWrite_o && !Branch_o && !Jump_o));

  // Mode-specific bundles
  assert property (@(Op_i) ##0 (Op_i==Op_lw)  -> (MemRead_o && MemtoReg_o && RegWrite_o &&  ALUSrc_o && !MemWrite_o && !Branch_o && !Jump_o && ALUOp_o==2'b00));
  assert property (@(Op_i) ##0 (Op_i==Op_sw)  -> (MemWrite_o && !MemRead_o && !MemtoReg_o && !RegWrite_o &&  ALUSrc_o && !Branch_o && !Jump_o && ALUOp_o==2'b00));
  assert property (@(Op_i) ##0 (Op_i==Op_beq) -> (Branch_o && !MemRead_o && !MemWrite_o && !MemtoReg_o && !RegWrite_o && !ALUSrc_o && !Jump_o && ALUOp_o==2'b01));
  assert property (@(Op_i) ##0 (Op_i==Op_ALU) -> (RegDst_o && !ALUSrc_o && RegWrite_o && !MemRead_o && !MemWrite_o && !MemtoReg_o && !Branch_o && !Jump_o && ALUOp_o==2'b10));
  assert property (@(Op_i) ##0 (Op_i==Op_addi)-> (!RegDst_o &&  ALUSrc_o && RegWrite_o && !MemRead_o && !MemWrite_o && !MemtoReg_o && !Branch_o && !Jump_o && ALUOp_o==2'b00));
  assert property (@(Op_i) ##0 (Op_i==Op_j)   -> (Jump_o && !Branch_o && !MemRead_o && !MemWrite_o && !MemtoReg_o && !RegWrite_o && !ALUSrc_o && ALUOp_o==2'b10));

  // Pattern-based checks unique to this design
  assert property (@(Op_i) ##0 (((Op_i & 6'b111110)==6'b000010) -> (RegDst_o && !ALUSrc_o))); // j/jal class
  assert property (@(Op_i) ##0 (((Op_i & 6'b111100)==6'b010000) -> (RegDst_o && !ALUSrc_o && !Jump_o && !Branch_o)));

  // Key functional coverage
  cover property (@(Op_i) ##0 (Op_i==Op_ALU));
  cover property (@(Op_i) ##0 (Op_i==Op_lw));
  cover property (@(Op_i) ##0 (Op_i==Op_sw));
  cover property (@(Op_i) ##0 (Op_i==Op_beq));
  cover property (@(Op_i) ##0 (Op_i==Op_addi));
  cover property (@(Op_i) ##0 (Op_i==Op_j));
  cover property (@(Op_i) ##0 (Op_i==Op_jal));
  cover property (@(Op_i) ##0 ((Op_i & 6'b111100)==6'b010000)); // COP0 class example

  // Cover each ALUOp encoding
  cover property (@(Op_i) ##0 (ALUOp_o==2'b00));
  cover property (@(Op_i) ##0 (ALUOp_o==2'b01));
  cover property (@(Op_i) ##0 (ALUOp_o==2'b10));

  // Cover each control going high at least once
  cover property (@(Op_i) ##0 RegDst_o);
  cover property (@(Op_i) ##0 Jump_o);
  cover property (@(Op_i) ##0 Branch_o);
  cover property (@(Op_i) ##0 MemRead_o);
  cover property (@(Op_i) ##0 MemtoReg_o);
  cover property (@(Op_i) ##0 MemWrite_o);
  cover property (@(Op_i) ##0 ALUSrc_o);
  cover property (@(Op_i) ##0 RegWrite_o);

endmodule

// Bind into all instances of Control
bind Control Control_sva #(.Op_lw(Op_lw), .Op_sw(Op_sw), .Op_beq(Op_beq), .Op_ALU(Op_ALU), .Op_j(Op_j), .Op_addi(Op_addi))
  Control_sva_i (.*);