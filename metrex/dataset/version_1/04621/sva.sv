// Bindable SVA checker for add_sub
// Bind example (provide a sampling clock from your TB):
//   bind add_sub add_sub_sva u_add_sub_sva(.clk(tb_clk), .A(A), .B(B), .C(C), .O(O), .CO(CO), .OV(OV));

module add_sub_sva #(parameter W=4)
(
  input logic                 clk,
  input logic [W-1:0]         A, B,
  input logic                 C,
  input logic [W-1:0]         O,
  input logic                 CO, OV
);

  // Combinational correctness checks (no clock needed)
  always_comb begin
    automatic logic [W:0] sum;
    sum = {1'b0, A} + {1'b0, B};
    assert ({CO, O} == sum)
      else $error("add_sub SVA: {CO,O} != A+B (A=%0h B=%0h got {CO,O}=%0h exp=%0h)", A, B, {CO,O}, sum);

    // Signed-overflow consistency (alternate formulation)
    assert (OV == ((A[W-1] == B[W-1]) && (O[W-1] != A[W-1])))
      else $error("add_sub SVA: OV wrong (A=%0h B=%0h O=%0h OV=%0b)", A, B, O, OV);
  end

  default clocking @(posedge clk); endclocking

  // Sanity: no X/Z on interface
  assert property (!$isunknown({A,B,C,O,CO,OV})));

  // Independence from C: outputs must not change when only C toggles
  assert property ( (A==$past(A) && B==$past(B) && C!=$past(C)) |-> $stable({O,CO,OV}) )
    else $error("add_sub SVA: outputs changed when only C toggled");

  // If signs differ, overflow must be 0
  assert property ( (A[W-1]^B[W-1]) |-> !OV )
    else $error("add_sub SVA: OV set when adding different signs");

  // Functional coverage
  // Carry/no-carry
  cover property ( ({1'b0,A}+{1'b0,B})[W] );          // carry generated
  cover property ( !(({1'b0,A}+{1'b0,B})[W]) );       // no carry

  // Signed overflows
  cover property ( (~A[W-1] & ~B[W-1] &  O[W-1]) );   // positive overflow
  cover property ( ( A[W-1] &  B[W-1] & ~O[W-1]) );   // negative overflow

  // Independence scenario hit: C toggles while A,B stable and outputs stable
  cover property ( A==$past(A) && B==$past(B) && C!=$past(C) && {O,CO,OV}==$past({O,CO,OV}) );

  // Exercise both C polarities
  cover property ( C );
  cover property ( !C );

endmodule