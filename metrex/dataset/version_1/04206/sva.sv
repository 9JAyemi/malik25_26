// SVA for m6502_alu
// Bind example (hook clk from TB):
// bind m6502_alu m6502_alu_asserts u_m6502_alu_asserts(.clk(tb_clk), .*);

module m6502_alu_asserts(
  input logic              clk,
  input logic [7:0]        operation,
  input logic [7:0]        op_a,
  input logic [7:0]        op_b,
  input logic              carry_in,
  input logic [7:0]        result,
  input logic              carry,
  input logic              zero,
  input logic              overflow
);

  default clocking cb @(posedge clk); endclocking

  // opcode mirror
  localparam [7:0] OP_AND = 8'h01;
  localparam [7:0] OP_OR  = 8'h02;
  localparam [7:0] OP_XOR = 8'h03;
  localparam [7:0] OP_NOT = 8'h04;

  localparam [7:0] OP_ASL = 8'h11;
  localparam [7:0] OP_ROL = 8'h12;
  localparam [7:0] OP_ASR = 8'h13;
  localparam [7:0] OP_ROR = 8'h14;

  localparam [7:0] OP_ADD = 8'h21;
  localparam [7:0] OP_INC = 8'h22;
  localparam [7:0] OP_SUB = 8'h23;
  localparam [7:0] OP_DEC = 8'h24;

  localparam [7:0] OP_CMP = 8'h31;

  // No X/Z on outputs when inputs known
  assert property (!$isunknown({operation,op_a,op_b,carry_in}) |-> !$isunknown({result,carry,zero,overflow}));

  // Logical ops
  assert property (operation==OP_AND |-> result==(op_a & op_b) && carry==1'b0 && zero==1'b0 && overflow==1'b0);
  assert property (operation==OP_OR  |-> result==(op_a | op_b) && carry==1'b0 && zero==1'b0 && overflow==1'b0);
  assert property (operation==OP_XOR |-> result==(op_a ^ op_b) && carry==1'b0 && zero==1'b0 && overflow==1'b0);
  assert property (operation==OP_NOT |-> result==(~op_a)       && carry==1'b0 && zero==1'b0 && overflow==1'b0);

  // Shifts/rotates
  assert property (operation==OP_ASL |-> result=={op_a[6:0],carry_in} && carry==op_a[7] && zero==1'b0 && overflow==1'b0);
  assert property (operation==OP_ROL |-> result=={op_a[6:0],op_a[7]}  && carry==op_a[7] && zero==1'b0 && overflow==1'b0);
  assert property (operation==OP_ASR |-> result=={carry_in,op_a[7:1]} && carry==op_a[0] && zero==1'b0 && overflow==1'b0);
  assert property (operation==OP_ROR |-> result=={op_a[0],op_a[7:1]}  && carry==op_a[0] && zero==1'b0 && overflow==1'b0);

  // Add / Inc
  assert property (operation==OP_ADD |-> {carry,result}==({1'b0,op_a}+{1'b0,op_b}+carry_in)
                                   && zero==1'b0
                                   && overflow==((op_a[7]==op_b[7]) && (result[7]!=op_a[7])));
  assert property (operation==OP_INC |-> {carry,result}==({1'b0,op_a}+9'd1)
                                   && zero==1'b0
                                   && overflow==((op_a[7]==1'b0) && (result[7]==1'b1)));

  // Sub / Dec
  assert property (operation==OP_SUB |-> result==(op_a - op_b)
                                   && carry==1'b0
                                   && zero==(result==8'h00)
                                   && overflow==((op_a[7]!=op_b[7]) && (op_a[7]!=result[7])));
  assert property (operation==OP_DEC |-> result==(op_a - 8'h01)
                                   && carry==1'b0
                                   && zero==1'b0
                                   && overflow==((op_a[7]==1'b1) && (result[7]==1'b0)));

  // Compare
  assert property (operation==OP_CMP |-> result==8'h00
                                   && carry==1'b0
                                   && overflow==1'b0
                                   && zero==(op_a==op_b));

  // Unimplemented/default opcodes => all-zero outputs
  assert property (!(operation inside {OP_AND,OP_OR,OP_XOR,OP_NOT,
                                       OP_ASL,OP_ROL,OP_ASR,OP_ROR,
                                       OP_ADD,OP_INC,OP_SUB,OP_DEC,
                                       OP_CMP})
                   |-> result==8'h00 && carry==1'b0 && zero==1'b0 && overflow==1'b0);

  // Minimal functional cross-checks
  assert property (operation==OP_ADD |-> {carry,result} == ({1'b0,op_a}+{1'b0,op_b}+carry_in)); // carry/result consistency

  // Coverage: opcodes
  cover property (operation==OP_AND);
  cover property (operation==OP_OR);
  cover property (operation==OP_XOR);
  cover property (operation==OP_NOT);
  cover property (operation==OP_ASL);
  cover property (operation==OP_ROL);
  cover property (operation==OP_ASR);
  cover property (operation==OP_ROR);
  cover property (operation==OP_ADD);
  cover property (operation==OP_INC);
  cover property (operation==OP_SUB);
  cover property (operation==OP_DEC);
  cover property (operation==OP_CMP);
  cover property (!(operation inside {OP_AND,OP_OR,OP_XOR,OP_NOT,OP_ASL,OP_ROL,OP_ASR,OP_ROR,OP_ADD,OP_INC,OP_SUB,OP_DEC,OP_CMP}));

  // Coverage: interesting flag cases
  cover property (operation==OP_ADD && carry);
  cover property (operation==OP_ADD && overflow);
  cover property (operation==OP_ADD && !carry && !overflow);
  cover property (operation==OP_INC && overflow);
  cover property (operation==OP_SUB && zero);
  cover property (operation==OP_SUB && overflow);
  cover property (operation==OP_DEC && overflow);
  cover property (operation==OP_ASL && op_a[7]); // carry set
  cover property (operation==OP_ASR && op_a[0]); // carry set
  cover property (operation==OP_ROL && op_a[7]); // carry set
  cover property (operation==OP_ROR && op_a[0]); // carry set
  cover property (operation==OP_ASL && carry_in);
  cover property (operation==OP_ASR && carry_in);
  cover property (operation==OP_CMP && zero);
  cover property (operation==OP_CMP && !zero);

endmodule