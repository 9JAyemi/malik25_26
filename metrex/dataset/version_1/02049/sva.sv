// SVA for nor_buf: check functional correctness, buffer transparency, and provide concise coverage.

module nor_buf_sva (
  input logic A, B, C,
  input logic Y,
  input logic nor_out_Y
);

  // Sample anytime any relevant signal changes
  default clocking cb @(A or B or C or Y or nor_out_Y); endclocking

  // Functional correctness (no X/Z on inputs)
  a_func_known: assert property (
    !$isunknown({A,B,C})
    |-> (Y === ~(A|B|C) && nor_out_Y === ~(A|B|C) && Y === nor_out_Y)
  );

  // Robust corners with possible X/Z on other inputs
  a_any1_low:  assert property ( (A===1 || B===1 || C===1) |-> (Y===1'b0 && nor_out_Y===1'b0) );
  a_all0_high: assert property ( (A===0 && B===0 && C===0) |-> (Y===1'b1 && nor_out_Y===1'b1) );

  // No spurious output change without input change
  a_no_spur_change: assert property ( $stable({A,B,C}) |-> ($stable(Y) && $stable(nor_out_Y)) );

  // Coverage: exercise all 8 input combinations
  generate
    for (genvar i=0; i<8; i++) begin : cov_vecs
      localparam logic [2:0] V = i[2:0];
      c_inputs: cover property ( {A,B,C} === V );
    end
  endgenerate

  // Coverage: output and input activity
  c_y_rise: cover property ($rose(Y));
  c_y_fall: cover property ($fell(Y));
  c_a_chg:  cover property ($changed(A));
  c_b_chg:  cover property ($changed(B));
  c_c_chg:  cover property ($changed(C));

endmodule

// Bind SVA into the DUT (includes internal wire nor_out_Y)
bind nor_buf nor_buf_sva u_nor_buf_sva (
  .A(A),
  .B(B),
  .C(C),
  .Y(Y),
  .nor_out_Y(nor_out_Y)
);