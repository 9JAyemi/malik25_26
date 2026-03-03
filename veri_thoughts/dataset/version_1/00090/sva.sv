// SVA for binary_adder/full_adder
// Bind modules only; no DUT/testbench changes required.

module full_adder_sva;
  // Bound into each full_adder instance; can directly see A,B,C_in,S,C_out
  event comb_ev;
  always @(A or B or C_in) -> comb_ev;

  // Functional correctness and X-prop
  assert property (@(comb_ev) {C_out,S} == A + B + C_in)
    else $error("full_adder func mismatch: A=%0b B=%0b Cin=%0b -> {C,S}=%0b%0b", A,B,C_in,C_out,S);

  assert property (@(comb_ev) (!$isunknown({A,B,C_in})) |-> (!$isunknown({S,C_out})))
    else $error("full_adder X/Z on outputs with known inputs");

  // Full input-space coverage (8 combos)
  cover property (@(comb_ev) {A,B,C_in} == 3'b000);
  cover property (@(comb_ev) {A,B,C_in} == 3'b001);
  cover property (@(comb_ev) {A,B,C_in} == 3'b010);
  cover property (@(comb_ev) {A,B,C_in} == 3'b011);
  cover property (@(comb_ev) {A,B,C_in} == 3'b100);
  cover property (@(comb_ev) {A,B,C_in} == 3'b101);
  cover property (@(comb_ev) {A,B,C_in} == 3'b110);
  cover property (@(comb_ev) {A,B,C_in} == 3'b111);
endmodule

module binary_adder_sva;
  // Bound into binary_adder; can directly see A,B,S,C and sub-instances fa0..fa3
  event comb_ev;
  always @(A or B) -> comb_ev;

  // Functional correctness and X-prop
  assert property (@(comb_ev) {C,S} == A + B)
    else $error("binary_adder func mismatch: A=%0h B=%0h -> {C,S}=%0b_%0h", A,B,C,S);

  assert property (@(comb_ev) (!$isunknown({A,B})) |-> (!$isunknown({S,C})))
    else $error("binary_adder X/Z on outputs with known inputs");

  // Structural/wiring checks
  assert property (@(comb_ev) (fa0.C_in == 1'b0))
    else $error("fa0 C_in not tied to 0");
  assert property (@(comb_ev) (fa1.C_in == fa0.C_out && fa2.C_in == fa1.C_out && fa3.C_in == fa2.C_out))
    else $error("Carry chain miswired");
  assert property (@(comb_ev) (C == fa3.C_out))
    else $error("Top carry-out mismatch");
  assert property (@(comb_ev) S == {fa3.S,fa2.S,fa1.S,fa0.S})
    else $error("Sum bit mapping mismatch");

  // Useful corner/feature coverage
  // Extremes and carry/no-carry
  cover property (@(comb_ev) A==4'h0 && B==4'h0 && {C,S}==5'h00);
  cover property (@(comb_ev) A==4'hF && B==4'h0 && {C,S}==5'h0F);
  cover property (@(comb_ev) A==4'h0 && B==4'hF && {C,S}==5'h0F);
  cover property (@(comb_ev) A==4'hF && B==4'hF && {C,S}==5'h1E);
  cover property (@(comb_ev) C==1'b0);
  cover property (@(comb_ev) C==1'b1);

  // Full ripple: generate at bit0, propagate through bits 1..3
  cover property (@(comb_ev) (A[0]&B[0]) && (A[1]^B[1]) && (A[2]^B[2]) && (A[3]^B[3]) && C);

  // Per-bit behavior coverage: generate/propagate/kill observed on each bit
  generate
    genvar i;
    for (i=0; i<4; i++) begin : bit_cov
      cover property (@(comb_ev) (A[i] & B[i]));       // generate
      cover property (@(comb_ev) (A[i] ^ B[i]));       // propagate
      cover property (@(comb_ev) (~A[i] & ~B[i]));     // kill
    end
  endgenerate
endmodule

// Bind into DUTs
bind full_adder   full_adder_sva    u_full_adder_sva();
bind binary_adder binary_adder_sva  u_binary_adder_sva();