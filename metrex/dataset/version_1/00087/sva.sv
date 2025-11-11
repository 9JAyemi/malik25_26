// SVA for sky130_fd_sc_hd__a31oi
// Function: Y = ~(B1 | (A1 & A2 & A3))

module sky130_fd_sc_hd__a31oi_sva (
  input logic A1, A2, A3, B1, Y,
  input logic and0_out, nor0_out_Y
);

  // Functional correctness (4-state aware)
  a_func: assert property (@(A1 or A2 or A3 or B1)
                          Y === ~(B1 | (A1 & A2 & A3)));

  // Structural checks on internal nets
  a_and0: assert property (@(A1 or A2 or A3)
                          and0_out === (A1 & A2 & A3));
  a_nor0: assert property (@(B1 or and0_out)
                          nor0_out_Y === ~(B1 | and0_out));
  a_buf0: assert property (@(nor0_out_Y or Y)
                          Y === nor0_out_Y);

  // Influence/masking behavior
  // B1 controls Y when and0_out==0
  a_b1_toggles_y_when_and0_is0:
    assert property (@(B1) (and0_out===1'b0 && $changed(B1)) |-> ($changed(Y) && Y===~B1));

  // B1 changes do not affect Y when and0_out==1
  a_b1_masked_when_and0_is1:
    assert property (@(B1) (and0_out===1'b1 && $changed(B1)) |-> !$changed(Y));

  // Any A toggle affects Y only when B1==0 and other As are 1
  a_a1_toggles_y:
    assert property (@(A1) (B1===1'b0 && A2===1'b1 && A3===1'b1 && $changed(A1)) |-> $changed(Y));
  a_a2_toggles_y:
    assert property (@(A2) (B1===1'b0 && A1===1'b1 && A3===1'b1 && $changed(A2)) |-> $changed(Y));
  a_a3_toggles_y:
    assert property (@(A3) (B1===1'b0 && A1===1'b1 && A2===1'b1 && $changed(A3)) |-> $changed(Y));

  // A changes do not affect Y when B1==1
  a_a_masked_when_b1_is1:
    assert property (@(A1 or A2 or A3) (B1===1'b1 && $changed({A1,A2,A3})) |-> !$changed(Y));

  // Basic determinism in key corners
  a_corner_b1_1:  assert property (@(B1) (B1===1'b1) |-> (Y===1'b0));
  a_corner_b1_0_and_anyA0: assert property (@(A1 or A2 or A3 or B1)
                             (B1===1'b0 && (A1===1'b0 || A2===1'b0 || A3===1'b0)) |-> (Y===1'b1));
  a_corner_all1:  assert property (@(A1 or A2 or A3 or B1)
                             (B1===1'b0 && A1===1'b1 && A2===1'b1 && A3===1'b1) |-> (Y===1'b0));

  // Coverage: both output values and control dominance cases
  c_y0: cover property (@(A1 or A2 or A3 or B1) Y===1'b0);
  c_y1: cover property (@(A1 or A2 or A3 or B1) Y===1'b1);

  c_b1_dominates: cover property (@(B1) $rose(B1) ##0 (Y===1'b0));
  c_and_dominates: cover property (@(A1 or A2 or A3)
                                   (B1===1'b0 && A1===1'b1 && A2===1'b1 && $rose(A3)) ##0 (Y===1'b0));

  c_b1_toggle_effect_when_and0_0:
    cover property (@(B1) (and0_out===1'b0 && $changed(B1)) ##0 $changed(Y));
  c_a_toggle_effect_when_b1_0:
    cover property (@(A1) (B1===1'b0 && A2===1'b1 && A3===1'b1 && $changed(A1)) ##0 $changed(Y));

endmodule

// Bind into the DUT to access internal nets
bind sky130_fd_sc_hd__a31oi sky130_fd_sc_hd__a31oi_sva i_a31oi_sva (
  .A1(A1), .A2(A2), .A3(A3), .B1(B1), .Y(Y),
  .and0_out(and0_out), .nor0_out_Y(nor0_out_Y)
);