// SVA for sky130_fd_sc_lp__a41oi
// Bind into the DUT to check functionality, internal nets, and provide concise coverage.

`ifndef A41OI_SVA
`define A41OI_SVA

module sky130_fd_sc_lp__a41oi_sva (
  input A1, A2, A3, A4, B1,
  input Y,
  input and0_out, nor0_out_Y
);

  // Sample on any relevant signal change; evaluate after ##0 to avoid delta races
  default clocking cb @(A1 or A2 or A3 or A4 or B1 or Y or and0_out or nor0_out_Y); endclocking

  // Top-level functional equivalence
  a_func: assert property (1'b1 |-> ##0 (Y === ~(B1 | (A1 & A2 & A3 & A4))));

  // Internal gate equivalence checks
  a_and:  assert property (1'b1 |-> ##0 (and0_out   === (A1 & A2 & A3 & A4)));
  a_nor:  assert property (1'b1 |-> ##0 (nor0_out_Y === ~(B1 | and0_out)));
  a_buf:  assert property (1'b1 |-> ##0 (Y === nor0_out_Y));

  // No spurious Y toggles without input activity
  a_no_spurious: assert property ($changed(Y) |-> $changed({A1,A2,A3,A4,B1}));

  // Deterministic dominance (X-tolerant) checks
  a_dom_b1:     assert property ((B1 === 1'b1)                                             |-> ##0 (Y === 1'b0));
  a_allA_high:  assert property ((B1 === 1'b0 && A1===1 && A2===1 && A3===1 && A4===1)     |-> ##0 (Y === 1'b0));
  a_anyA_zero:  assert property ((B1 === 1'b0 && (A1===0 || A2===0 || A3===0 || A4===0))   |-> ##0 (Y === 1'b1));

  // Coverage: key functional scenarios and Y toggles
  c_y0_b1:      cover property ( (B1==1)                                      ##0 (Y==0) );
  c_y0_allA:    cover property ( (B1==0 && A1==1 && A2==1 && A3==1 && A4==1)  ##0 (Y==0) );
  c_y1_anyA0:   cover property ( (B1==0 && (A1==0 || A2==0 || A3==0 || A4==0))##0 (Y==1) );
  c_y_rise:     cover property ( $rose(Y) );
  c_y_fall:     cover property ( $fell(Y) );

endmodule

bind sky130_fd_sc_lp__a41oi sky130_fd_sc_lp__a41oi_sva sva_i (.*);

`endif