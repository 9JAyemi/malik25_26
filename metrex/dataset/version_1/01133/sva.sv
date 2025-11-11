// SVA checker for four_bit_adder
// Concise, high-quality checks and essential coverage

`default_nettype none

module four_bit_adder_sva (
  input logic [3:0] A,
  input logic [3:0] B,
  input logic [3:0] S,
  input logic       Cout
);

  // Sample on any input change
  event ev;
  always @(A or B) -> ev;

  // Assertions
  // 1) Arithmetic correctness (5-bit sum must match {Cout,S})
  assert property (@(ev) !$isunknown({A,B}) |-> {Cout, S} == (A + B))
    else $error("four_bit_adder: {Cout,S} != A+B");

  // 2) No X/Z on outputs when inputs are known
  assert property (@(ev) !$isunknown({A,B}) |-> !$isunknown({S,Cout}))
    else $error("four_bit_adder: X/Z on outputs with known inputs");

  // Coverage
  // Corner cases
  cover property (@(ev) (A==4'h0 && B==4'h0));
  cover property (@(ev) (A==4'hF && B==4'h0));
  cover property (@(ev) (A==4'h0 && B==4'hF));
  cover property (@(ev) (A==4'hF && B==4'hF));     // expect carry
  cover property (@(ev) ((A+B) == 5'd16));         // boundary carry
  cover property (@(ev) ((A+B) == 5'd31));         // max sum
  cover property (@(ev) Cout);                     // carry observed

  // Hit all 4-bit sum values at least once
  genvar i;
  generate
    for (i=0; i<16; i++) begin : cov_s_vals
      cover property (@(ev) S == i[3:0]);
    end
  endgenerate

endmodule

// Bind into DUT
bind four_bit_adder four_bit_adder_sva sva_inst (
  .A(A), .B(B), .S(S), .Cout(Cout)
);