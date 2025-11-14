// SVA checker for ControlUnit
// Bind this module to the DUT: bind ControlUnit ControlUnit_sva dut_sva (.*);

module ControlUnit_sva(
  input  logic [5:0] Special,
  input  logic [5:0] instructionCode,
  input  logic       RegDst,
  input  logic       Branch,
  input  logic       BranchType,
  input  logic       MemtoReg,
  input  logic [3:0] MemWrite,
  input  logic       ALUSrc,
  input  logic       ALUShiftImm,
  input  logic       RegWrite,
  input  logic       LoadImm,
  input  logic       ZeroEx,
  input  logic       EOP,
  input  logic [1:0] memReadWidth,
  input  logic [3:0] aluOperation
);

  // Sample on any change to the combinational inputs
  default clocking cb @(Special or instructionCode); endclocking

  // Helper sets
  let special_list = {6'b100000,6'b100001,6'b100011,6'b100111,6'b100100,6'b100101,
                      6'b101000,6'b101001,6'b101011,6'b001000,6'b001100,6'b001101,
                      6'b001110,6'b001010,6'b001111,6'b000100,6'b000101,6'b111111};
  let default_path = !(Special inside special_list);

  // Generic invariants
  a_branch_type_only_with_branch: assert property (BranchType |-> ##0 Branch);
  a_loads_invariant:              assert property (MemtoReg |-> ##0 (RegWrite && !Branch && !EOP && MemWrite==4'd0 && ALUSrc && aluOperation==4'd3));
  a_stores_invariant:             assert property ((MemWrite!=4'd0) |-> ##0 (!RegWrite && !MemtoReg && !Branch && !EOP && ALUSrc && aluOperation==4'd3 && memReadWidth==2'd0));
  a_branch_invariant:             assert property (Branch |-> ##0 (!RegWrite && !MemtoReg && MemWrite==4'd0 && !EOP && !ALUSrc && aluOperation==4'd4 && memReadWidth==2'd0));
  a_eop_invariant:                assert property (EOP |-> ##0 (!RegWrite && !MemtoReg && !Branch && MemWrite==4'd0 && ALUSrc && ZeroEx && aluOperation==4'd6 && memReadWidth==2'd0));

  // All explicit Special cases: outputs must match exactly
  a_s_100000: assert property (Special==6'b100000 |-> ##0 (EOP==0 && RegDst==0 && Branch==0 && BranchType==0 && MemtoReg==1 && MemWrite==4'd0 && ALUSrc==1 && ALUShiftImm==0 && RegWrite==1 && LoadImm==0 && ZeroEx==0 && aluOperation==4'd3 && memReadWidth==2));
  a_s_100001: assert property (Special==6'b100001 |-> ##0 (EOP==0 && RegDst==0 && Branch==0 && BranchType==0 && MemtoReg==1 && MemWrite==4'd0 && ALUSrc==1 && ALUShiftImm==0 && RegWrite==1 && LoadImm==0 && ZeroEx==0 && aluOperation==4'd3 && memReadWidth==1));
  a_s_100011: assert property (Special==6'b100011 |-> ##0 (EOP==0 && RegDst==0 && Branch==0 && BranchType==0 && MemtoReg==1 && MemWrite==4'd0 && ALUSrc==1 && ALUShiftImm==0 && RegWrite==1 && LoadImm==0 && ZeroEx==0 && aluOperation==4'd3 && memReadWidth==0));
  a_s_100111: assert property (Special==6'b100111 |-> ##0 (EOP==0 && RegDst==0 && Branch==0 && BranchType==0 && MemtoReg==1 && MemWrite==4'd0 && ALUSrc==1 && ALUShiftImm==0 && RegWrite==1 && LoadImm==0 && ZeroEx==0 && aluOperation==4'd3 && memReadWidth==0));
  a_s_100100: assert property (Special==6'b100100 |-> ##0 (EOP==0 && RegDst==0 && Branch==0 && BranchType==0 && MemtoReg==1 && MemWrite==4'd0 && ALUSrc==1 && ALUShiftImm==0 && RegWrite==1 && LoadImm==0 && ZeroEx==0 && aluOperation==4'd3 && memReadWidth==2));
  a_s_100101: assert property (Special==6'b100101 |-> ##0 (EOP==0 && RegDst==0 && Branch==0 && BranchType==0 && MemtoReg==1 && MemWrite==4'd0 && ALUSrc==1 && ALUShiftImm==0 && RegWrite==1 && LoadImm==0 && ZeroEx==0 && aluOperation==4'd3 && memReadWidth==1));

  a_s_101000: assert property (Special==6'b101000 |-> ##0 (EOP==0 && RegDst==0 && Branch==0 && BranchType==0 && MemtoReg==0 && MemWrite==4'd1    && ALUSrc==1 && ALUShiftImm==0 && RegWrite==0 && LoadImm==0 && ZeroEx==0 && aluOperation==4'd3 && memReadWidth==0));
  a_s_101001: assert property (Special==6'b101001 |-> ##0 (EOP==0 && RegDst==0 && Branch==0 && BranchType==0 && MemtoReg==0 && MemWrite==4'b0011 && ALUSrc==1 && ALUShiftImm==0 && RegWrite==0 && LoadImm==0 && ZeroEx==0 && aluOperation==4'd3 && memReadWidth==0));
  a_s_101011: assert property (Special==6'b101011 |-> ##0 (EOP==0 && RegDst==0 && Branch==0 && BranchType==0 && MemtoReg==0 && MemWrite==4'b1111 && ALUSrc==1 && ALUShiftImm==0 && RegWrite==0 && LoadImm==0 && ZeroEx==0 && aluOperation==4'd3 && memReadWidth==0));

  a_s_001000: assert property (Special==6'b001000 |-> ##0 (EOP==0 && RegDst==0 && Branch==0 && BranchType==0 && MemtoReg==0 && MemWrite==4'd0 && ALUSrc==1 && ALUShiftImm==0 && RegWrite==1 && LoadImm==0 && ZeroEx==0 && aluOperation==4'd3 && memReadWidth==0));
  a_s_001100: assert property (Special==6'b001100 |-> ##0 (EOP==0 && RegDst==0 && Branch==0 && BranchType==0 && MemtoReg==0 && MemWrite==4'd0 && ALUSrc==1 && ALUShiftImm==0 && RegWrite==1 && LoadImm==0 && ZeroEx==1 && aluOperation==4'd5 && memReadWidth==0));
  a_s_001101: assert property (Special==6'b001101 |-> ##0 (EOP==0 && RegDst==0 && Branch==0 && BranchType==0 && MemtoReg==0 && MemWrite==4'd0 && ALUSrc==1 && ALUShiftImm==0 && RegWrite==1 && LoadImm==0 && ZeroEx==1 && aluOperation==4'd6 && memReadWidth==0));
  a_s_001110: assert property (Special==6'b001110 |-> ##0 (EOP==0 && RegDst==0 && Branch==0 && BranchType==0 && MemtoReg==0 && MemWrite==4'd0 && ALUSrc==1 && ALUShiftImm==0 && RegWrite==1 && LoadImm==0 && ZeroEx==1 && aluOperation==4'd7 && memReadWidth==0));
  a_s_001010: assert property (Special==6'b001010 |-> ##0 (EOP==0 && RegDst==0 && Branch==0 && BranchType==0 && MemtoReg==0 && MemWrite==4'd0 && ALUSrc==1 && ALUShiftImm==0 && RegWrite==1 && LoadImm==0 && ZeroEx==0 && aluOperation==4'd9 && memReadWidth==0));
  a_s_001111: assert property (Special==6'b001111 |-> ##0 (EOP==0 && RegDst==0 && Branch==0 && BranchType==0 && MemtoReg==0 && MemWrite==4'd0 && ALUSrc==1 && ALUShiftImm==0 && RegWrite==1 && LoadImm==1 && ZeroEx==0 && aluOperation==4'd0 && memReadWidth==0));

  a_s_000100: assert property (Special==6'b000100 |-> ##0 (EOP==0 && RegDst==0 && Branch==1 && BranchType==0 && MemtoReg==0 && MemWrite==4'd0 && ALUSrc==0 && ALUShiftImm==0 && RegWrite==0 && LoadImm==0 && ZeroEx==0 && aluOperation==4'd4 && memReadWidth==0));
  a_s_000101: assert property (Special==6'b000101 |-> ##0 (EOP==0 && RegDst==0 && Branch==1 && BranchType==1 && MemtoReg==0 && MemWrite==4'd0 && ALUSrc==0 && ALUShiftImm==0 && RegWrite==0 && LoadImm==0 && ZeroEx==0 && aluOperation==4'd4 && memReadWidth==0));

  a_s_111111: assert property (Special==6'b111111 |-> ##0 (EOP==1 && RegDst==0 && Branch==0 && BranchType==0 && MemtoReg==0 && MemWrite==4'd0 && ALUSrc==1 && ALUShiftImm==0 && RegWrite==0 && LoadImm==0 && ZeroEx==1 && aluOperation==4'd6 && memReadWidth==0));

  // In all explicit Special cases, ALUShiftImm must be 0
  a_shiftimm_zero_on_specials: assert property ((Special inside special_list) |-> ##0 (ALUShiftImm==0));

  // Default path (R-type) invariants
  a_default_fixed_controls: assert property (default_path |-> ##0 (EOP==0 && RegDst==1 && Branch==0 && BranchType==0 && MemtoReg==0 && MemWrite==4'd0 && ALUSrc==0 && RegWrite==1 && LoadImm==0 && ZeroEx==0 && memReadWidth==0));
  a_default_shiftimm:       assert property (default_path && (instructionCode inside {6'b000000,6'b000010,6'b000011}) |-> ##0 ALUShiftImm==1);
  a_default_shiftimm_else:  assert property (default_path && !(instructionCode inside {6'b000000,6'b000010,6'b000011}) |-> ##0 ALUShiftImm==0);

  // Default path ALU operation decode
  a_def_alop_000000: assert property (default_path && instructionCode==6'b000000 |-> ##0 aluOperation==4'd0);
  a_def_alop_000010: assert property (default_path && instructionCode==6'b000010 |-> ##0 aluOperation==4'd1);
  a_def_alop_000011: assert property (default_path && instructionCode==6'b000011 |-> ##0 aluOperation==4'd2);
  a_def_alop_000110: assert property (default_path && instructionCode==6'b000110 |-> ##0 aluOperation==4'd1);
  a_def_alop_000111: assert property (default_path && instructionCode==6'b000111 |-> ##0 aluOperation==4'd2);
  a_def_alop_000100: assert property (default_path && instructionCode==6'b000100 |-> ##0 aluOperation==4'd0);
  a_def_alop_100000: assert property (default_path && instructionCode==6'b100000 |-> ##0 aluOperation==4'd3);
  a_def_alop_100010: assert property (default_path && instructionCode==6'b100010 |-> ##0 aluOperation==4'd4);
  a_def_alop_100100: assert property (default_path && instructionCode==6'b100100 |-> ##0 aluOperation==4'd5);
  a_def_alop_100101: assert property (default_path && instructionCode==6'b100101 |-> ##0 aluOperation==4'd6);
  a_def_alop_100110: assert property (default_path && instructionCode==6'b100110 |-> ##0 aluOperation==4'd7);
  a_def_alop_100111: assert property (default_path && instructionCode==6'b100111 |-> ##0 aluOperation==4'd8);
  a_def_alop_101010: assert property (default_path && instructionCode==6'b101010 |-> ##0 aluOperation==4'd9);
  a_def_alop_default: assert property (default_path && !(instructionCode inside {6'b000000,6'b000010,6'b000011,6'b000110,6'b000111,6'b000100,6'b100000,6'b100010,6'b100100,6'b100101,6'b100110,6'b100111,6'b101010}) |-> ##0 aluOperation==4'hF);

  // Functional coverage
  c_specials: cover property (Special inside special_list);
  c_load_lb:  cover property (Special==6'b100000);
  c_load_lh:  cover property (Special==6'b100001);
  c_load_lw:  cover property (Special==6'b100011);
  c_load_lbu: cover property (Special==6'b100100);
  c_load_lhu: cover property (Special==6'b100101);
  c_load_lwu: cover property (Special==6'b100111);
  c_store_sb: cover property (Special==6'b101000);
  c_store_sh: cover property (Special==6'b101001);
  c_store_sw: cover property (Special==6'b101011);
  c_addi:     cover property (Special==6'b001000);
  c_andi:     cover property (Special==6'b001100);
  c_ori:      cover property (Special==6'b001101);
  c_xori:     cover property (Special==6'b001110);
  c_slti:     cover property (Special==6'b001010);
  c_lui:      cover property (Special==6'b001111);
  c_beq:      cover property (Special==6'b000100);
  c_bne:      cover property (Special==6'b000101);
  c_eop:      cover property (Special==6'b111111);

  // Default path coverage (R-type decode)
  c_default_path:       cover property (default_path);
  c_def_shift_ops:      cover property (default_path && (instructionCode inside {6'b000000,6'b000010,6'b000011}));
  c_def_alu_ops:        cover property (default_path && (instructionCode inside {6'b000110,6'b000111,6'b000100,6'b100000,6'b100010,6'b100100,6'b100101,6'b100110,6'b100111,6'b101010}));
  c_def_alu_default:    cover property (default_path && !(instructionCode inside {6'b000000,6'b000010,6'b000011,6'b000110,6'b000111,6'b000100,6'b100000,6'b100010,6'b100100,6'b100101,6'b100110,6'b100111,6'b101010}));

endmodule

// Bind into DUT
bind ControlUnit ControlUnit_sva dut_sva (.*);