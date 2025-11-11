// SVA for full_adder and ripple_carry_adder
// Combinational checks sample at ##0 to avoid delta-glitch sensitivity

module fa_sva(input sum, carry_out, input a, b, carry_in);
  default clocking cb @($global_clock); endclocking

  // Functional equivalence
  assert property (##0 {carry_out, sum} == a + b + carry_in);
  assert property (##0 carry_out == ((a & b) | ((a ^ b) & carry_in)));

  // X-prop guard
  assert property (!$isunknown({a,b,carry_in}) |-> ##0 !$isunknown({sum,carry_out}));

  // Truth-table coverage (all 8 input combinations)
  cover property (##0 {a,b,carry_in} == 3'b000);
  cover property (##0 {a,b,carry_in} == 3'b001);
  cover property (##0 {a,b,carry_in} == 3'b010);
  cover property (##0 {a,b,carry_in} == 3'b011);
  cover property (##0 {a,b,carry_in} == 3'b100);
  cover property (##0 {a,b,carry_in} == 3'b101);
  cover property (##0 {a,b,carry_in} == 3'b110);
  cover property (##0 {a,b,carry_in} == 3'b111);
endmodule

module rca_sva(input [3:0] S, input Cout, input [3:0] A, B, input Cin, input [2:0] c);
  default clocking cb @($global_clock); endclocking

  // Top-level equivalence
  assert property (##0 {Cout, S} == A + B + Cin);

  // Per-stage sum/carry correctness
  assert property (##0 {c[0], S[0]} == A[0] + B[0] + Cin);
  assert property (##0 {c[1], S[1]} == A[1] + B[1] + c[0]);
  assert property (##0 {c[2], S[2]} == A[2] + B[2] + c[1]);
  assert property (##0 {Cout, S[3]} == A[3] + B[3] + c[2]);

  // Carry-out factoring per bit
  assert property (##0 c[0] == ((A[0] & B[0]) | ((A[0] ^ B[0]) & Cin)));
  assert property (##0 c[1] == ((A[1] & B[1]) | ((A[1] ^ B[1]) & c[0])));
  assert property (##0 c[2] == ((A[2] & B[2]) | ((A[2] ^ B[2]) & c[1])));

  // X-prop guard (includes internal carries)
  assert property (!$isunknown({A,B,Cin}) |-> ##0 !$isunknown({S,Cout,c}));

  // Coverage: carry chain lengths and full propagate case
  cover property (##0 !c[0]);                                    // no carry from bit0
  cover property (##0 c[0] && !c[1]);                            // chain length 1
  cover property (##0 c[0] && c[1] && !c[2]);                    // chain length 2
  cover property (##0 c[0] && c[1] && c[2] && !Cout);            // chain length 3
  cover property (##0 c[0] && c[1] && c[2] && Cout);             // full ripple to MSB

  cover property (##0 ((A ^ B) == 4'hF) && Cin && (S == 4'h0) && Cout); // full propagate
endmodule

// Bind SVA to DUTs
bind full_adder           fa_sva  fa_sva_i(.*);
bind ripple_carry_adder   rca_sva rca_sva_i(.*);