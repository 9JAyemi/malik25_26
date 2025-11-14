// SVA for shifter — concise, full functional checks + key coverage
module shifter_sva (
  input  logic [31:0] A, B, Result,
  input  logic        aluc1, aluc0,
  input  logic        Zero, Carry, Negative, Overflow,
  // internal regs (to check internal intent/typos)
  input  logic [31:0] Result_temp,
  input  logic        Zero_temp, Carry_temp, Nagative_temp, Overflow_temp,
  input  logic [4:0]  shift_amount
);

  // Sample on any input change
  default clocking cb @(A or B or aluc1 or aluc0); endclocking

  // Known-propagation: if inputs known, outputs must be known
  assert property (!$isunknown({A,B,aluc1,aluc0}) |-> !$isunknown({Result,Zero,Carry,Negative,Overflow}));

  // Internal wiring/assignment sanity
  assert property (shift_amount == A[4:0]);
  assert property (Result   == Result_temp);
  assert property (Zero     == Zero_temp);
  assert property (Carry    == Carry_temp);
  assert property (Negative == Nagative_temp);
  assert property (Overflow == Overflow_temp);

  // ASR (aluc=00)
  assert property (({aluc1,aluc0}==2'b00) |->
    ( Result   == ($signed(B) >>> A[4:0]) &&
      Carry    == ((A[4:0]==5'd0) ? 1'b0 : B[A[4:0]-1]) &&
      Zero     == (Result==32'h0) &&
      Negative == Result[31] &&
      Overflow == 1'b0 ));

  // LSR (aluc=01)
  assert property (({aluc1,aluc0}==2'b01) |->
    ( Result   == (B >> A[4:0]) &&
      Carry    == ((A[4:0]==5'd0) ? 1'b0 : B[A[4:0]-1]) &&
      Zero     == (Result==32'h0) &&
      Negative == Result[31] &&
      Overflow == 1'b0 ));

  // LSL (aluc=10 or 11)
  assert property ((aluc1==1'b1) |->
    ( Result   == (B << A[4:0]) &&
      Carry    == ((A[4:0]==5'd0) ? 1'b0 : B[32 - A[4:0]]) &&
      Zero     == (Result==32'h0) &&
      Negative == Result[31] &&
      Overflow == 1'b0 ));

  // Opcode coverage
  cover property ({aluc1,aluc0}==2'b00);
  cover property ({aluc1,aluc0}==2'b01);
  cover property ({aluc1,aluc0}==2'b10);
  cover property ({aluc1,aluc0}==2'b11);

  // Corner shift amounts per operation
  cover property (({aluc1,aluc0}==2'b00) && (A[4:0]==5'd0));
  cover property (({aluc1,aluc0}==2'b00) && (A[4:0]==5'd1));
  cover property (({aluc1,aluc0}==2'b00) && (A[4:0]==5'd31));

  cover property (({aluc1,aluc0}==2'b01) && (A[4:0]==5'd0));
  cover property (({aluc1,aluc0}==2'b01) && (A[4:0]==5'd1));
  cover property (({aluc1,aluc0}==2'b01) && (A[4:0]==5'd31));

  cover property ((aluc1==1'b1) && (A[4:0]==5'd0));
  cover property ((aluc1==1'b1) && (A[4:0]==5'd1));
  cover property ((aluc1==1'b1) && (A[4:0]==5'd31));

  // ASR sign-extension scenario (negative B and nonzero shift)
  cover property (({aluc1,aluc0}==2'b00) && (A[4:0] inside {5'd1,5'd31}) && B[31] && Negative);

endmodule

bind shifter shifter_sva
(
  .A(A), .B(B), .Result(Result),
  .aluc1(aluc1), .aluc0(aluc0),
  .Zero(Zero), .Carry(Carry), .Negative(Negative), .Overflow(Overflow),
  .Result_temp(Result_temp), .Zero_temp(Zero_temp), .Carry_temp(Carry_temp),
  .Nagative_temp(Nagative_temp), .Overflow_temp(Overflow_temp), .shift_amount(shift_amount)
);