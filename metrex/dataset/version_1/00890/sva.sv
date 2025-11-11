// SVA checker for alu. Bind this to the DUT.
// Focused, concise assertions with full opcode and flag checking plus coverage.

module alu_sva (
  input  logic [15:0] A, B,
  input  logic [3:0]  function_sel,
  input  logic [15:0] aluout,
  input  logic        zero_flag, parity_flag, carry_flag
);

  // Opcode encodings (mirror DUT)
  localparam logic [3:0]
    MOVE = 4'b0000,
    COMP = 4'b0001,
    AND_ = 4'b0010,
    OR_  = 4'b0011,
    XOR_ = 4'b0100,
    ADD  = 4'b0101,
    INCR = 4'b0110,
    SUB  = 4'b0111,
    ROTL = 4'b1000,
    LSHL = 4'b1001,
    ROTR = 4'b1010,
    LSHR = 4'b1011,
    XNOR = 4'b1100,
    NOR  = 4'b1101,
    DECR = 4'b1110,
    NAND = 4'b1111;

  // Clocking for combinational logic: sample on any input change; check at ##0
  default clocking cb @(A or B or function_sel); endclocking
  default disable iff ($isunknown({A,B,function_sel}));

  // Outputs must be known whenever inputs are known
  assert property (1'b1 |-> ##0 !$isunknown({aluout, zero_flag, parity_flag, carry_flag}));

  // Global flag correctness
  assert property (1'b1 |-> ##0 (zero_flag == ~|aluout));
  assert property (1'b1 |-> ##0 (parity_flag == ^aluout));

  // Per-op correctness
  assert property ((function_sel==MOVE) |-> ##0 (carry_flag==1'b0 && aluout==B));
  assert property ((function_sel==COMP) |-> ##0 (carry_flag==1'b1 && aluout==~B));
  assert property ((function_sel==AND_) |-> ##0 (carry_flag==1'b0 && aluout==(A & B)));
  assert property ((function_sel==OR_)  |-> ##0 (carry_flag==1'b0 && aluout==(A | B)));
  assert property ((function_sel==XOR_) |-> ##0 (carry_flag==1'b0 && aluout==(A ^ B)));
  assert property ((function_sel==ADD)  |-> ##0 ({carry_flag, aluout} == (A + B)));
  assert property ((function_sel==INCR) |-> ##0 ({carry_flag, aluout} == (B + 1)));
  assert property ((function_sel==SUB)  |-> ##0 ({carry_flag, aluout} == ({1'b1, A} - B)));
  assert property ((function_sel==ROTL) |-> ##0 (carry_flag==B[15] && aluout=={B[14:0], B[15]}));
  assert property ((function_sel==LSHL) |-> ##0 (carry_flag==B[15] && aluout=={B[14:0], 1'b0}));
  assert property ((function_sel==ROTR) |-> ##0 (carry_flag==B[0]  && aluout=={B[0], B[15:1]}));
  assert property ((function_sel==LSHR) |-> ##0 (carry_flag==1'b0  && aluout=={1'b0, B[15:1]}));
  assert property ((function_sel==XNOR) |-> ##0 (carry_flag==1'b1 && aluout==(A ~^ B)));
  assert property ((function_sel==NOR)  |-> ##0 (carry_flag==1'b1 && aluout==~(A | B)));
  assert property ((function_sel==DECR) |-> ##0 ({carry_flag, aluout} == (B - 1)));
  assert property ((function_sel==NAND) |-> ##0 (carry_flag==1'b1 && aluout==~(A & B)));

  // Compact functional coverage
  cover property (function_sel==MOVE);
  cover property (function_sel==COMP);
  cover property (function_sel==AND_);
  cover property (function_sel==OR_);
  cover property (function_sel==XOR_);
  cover property (function_sel==ADD);
  cover property (function_sel==INCR);
  cover property (function_sel==SUB);
  cover property (function_sel==ROTL);
  cover property (function_sel==LSHL);
  cover property (function_sel==ROTR);
  cover property (function_sel==LSHR);
  cover property (function_sel==XNOR);
  cover property (function_sel==NOR);
  cover property (function_sel==DECR);
  cover property (function_sel==NAND);

  // Arithmetic corner coverage (input-based, not relying on DUT outputs)
  cover property (function_sel==ADD  && ({1'b0,A}+{1'b0,B})[16]==1'b0); // no carry
  cover property (function_sel==ADD  && ({1'b0,A}+{1'b0,B})[16]==1'b1); // carry
  cover property (function_sel==INCR && B==16'hFFFF);                    // wrap
  cover property (function_sel==DECR && B==16'h0000);                    // borrow/wrap
  cover property (function_sel==SUB  && ({1'b1,A}-{1'b0,B})[16]==1'b1);  // no borrow
  cover property (function_sel==SUB  && ({1'b1,A}-{1'b0,B})[16]==1'b0);  // borrow

  // Flag coverage
  cover property (zero_flag==1'b1);
  cover property (parity_flag==1'b0);
  cover property (parity_flag==1'b1);

endmodule

// Bind into DUT
bind alu alu_sva alu_sva_i (
  .A(A), .B(B), .function_sel(function_sel),
  .aluout(aluout), .zero_flag(zero_flag),
  .parity_flag(parity_flag), .carry_flag(carry_flag)
);