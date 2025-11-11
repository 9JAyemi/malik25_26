// SVA for add8bit: checks full 9-bit addition correctness, X-prop, and key corner cases.
// Bindable checker; no DUT changes needed.

module add8bit_sva (
  input  logic [7:0] A,
  input  logic [7:0] B,
  input  logic       Cin,
  input  logic       Cout,
  input  logic [7:0] C
);
  // Helpers
  let inputs_known = !$isunknown({A,B,Cin});
  let sum9 = {1'b0, A} + {1'b0, B} + Cin;

  // Core functional correctness: 9-bit sum must match {Cout,C}
  assert property (@(A or B or Cin) inputs_known |-> {Cout, C} == sum9)
    else $error("add8bit sum mismatch: A=%0h B=%0h Cin=%0b -> C=%0h Cout=%0b (exp=%0h)",
                A, B, Cin, C, Cout, sum9);

  // No X/Z on outputs when inputs are known
  assert property (@(A or B or Cin) inputs_known |-> !$isunknown({Cout, C}))
    else $error("add8bit X/Z on outputs for known inputs: A=%0h B=%0h Cin=%0b C=%0h Cout=%0b",
                A, B, Cin, C, Cout);

  // Minimal but meaningful functional coverage
  cover property (@(A or B or Cin) inputs_known && A==8'h00 && B==8'h00 && Cin==1'b0 && C==8'h00 && Cout==1'b0); // zero + zero
  cover property (@(A or B or Cin) inputs_known && A==8'h00 && B==8'h00 && Cin==1'b1 && C==8'h01 && Cout==1'b0); // carry-in only
  cover property (@(A or B or Cin) inputs_known && A==8'h80 && B==8'h80 && Cin==1'b0 && C==8'h00 && Cout==1'b1); // MSB carry generate
  cover property (@(A or B or Cin) inputs_known && (A^B)==8'hFF && Cin==1'b1 && C==8'h00 && Cout==1'b1);        // full propagate chain
  cover property (@(A or B or Cin) inputs_known && A==8'hFF && B==8'h01 && Cin==1'b0 && C==8'h00 && Cout==1'b1); // wrap to zero
endmodule

bind add8bit add8bit_sva u_add8bit_sva(.A(A), .B(B), .Cin(Cin), .Cout(Cout), .C(C));