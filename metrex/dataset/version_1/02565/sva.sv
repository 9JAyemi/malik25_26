// SVA for mux4to1_4bit
// Checks intended 4:1 mux behavior and provides concise coverage.

module mux4to1_4bit_sva (
  input  logic [3:0] A, B, C, D,
  input  logic       S0, S1,
  input  logic [3:0] Y
);

  // Functional correctness: 00->A, 01->B, 10->C, 11->D
  property p_functional_sel;
    @(A or B or C or D or S0 or S1 or Y)
      !$isunknown({S1,S0}) |->
        (({S1,S0}==2'b00 && Y===A) ||
         ({S1,S0}==2'b01 && Y===B) ||
         ({S1,S0}==2'b10 && Y===C) ||
         ({S1,S0}==2'b11 && Y===D));
  endproperty
  assert property (p_functional_sel);

  // No X on Y when selects and all inputs are known
  property p_no_x_when_known;
    @(A or B or C or D or S0 or S1 or Y)
      !$isunknown({A,B,C,D,S1,S0}) |->
      !$isunknown(Y);
  endproperty
  assert property (p_no_x_when_known);

  // Idempotence: if all inputs equal (bitwise), Y must equal that value regardless of selects
  property p_all_equal_passthrough;
    @(A or B or C or D or S0 or S1 or Y)
      ((A===B) && (B===C) && (C===D)) |->
      (Y===A);
  endproperty
  assert property (p_all_equal_passthrough);

  // Coverage: each select combination observed with correct output
  cover property (@(A or B or C or D or S0 or S1 or Y)
                  {S1,S0}==2'b00 && Y===A);
  cover property (@(A or B or C or D or S0 or S1 or Y)
                  {S1,S0}==2'b01 && Y===B);
  cover property (@(A or B or C or D or S0 or S1 or Y)
                  {S1,S0}==2'b10 && Y===C);
  cover property (@(A or B or C or D or S0 or S1 or Y)
                  {S1,S0}==2'b11 && Y===D);

  // Coverage: select line activity
  cover property (@(S0) $rose(S0));
  cover property (@(S0) $fell(S0));
  cover property (@(S1) $rose(S1));
  cover property (@(S1) $fell(S1));

endmodule

bind mux4to1_4bit mux4to1_4bit_sva sva_mux4to1_4bit (.*);