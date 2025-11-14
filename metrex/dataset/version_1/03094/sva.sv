// SVA checker for divider; bind this to the DUT
module divider_sva (
  input logic        clk,
  input logic [7:0]  div,
  input logic [7:0]  dvr,
  input logic [7:0]  quotient,
  input logic [7:0]  remainder
);

  default clocking cb @(posedge clk); endclocking

  // Sanity (no X/Z on IOs at sampling edge)
  a_no_x_inputs:  assert property (!$isunknown({div,dvr}));
  a_no_x_outputs: assert property (!$isunknown({quotient,remainder}));

  // Core functional correctness (for nonzero divisor)
  a_exact_fn:     assert property ( (dvr != 8'h00) |-> (quotient == (div / dvr) && remainder == (div % dvr)) );
  a_rem_bound:    assert property ( (dvr != 8'h00) |-> (remainder < dvr) );

  // Defined divide-by-zero behavior per RTL
  a_div0_impl:    assert property ( (dvr == 8'h00) |-> (quotient == 8'hFF && remainder == div) );

  // Stateless/pure function w.r.t. inputs
  a_pure_fn:      assert property ( $past(1'b1) |-> ((div == $past(div) && dvr == $past(dvr)) |-> (quotient == $past(quotient) && remainder == $past(remainder))) );

  // Useful corner cases
  a_dvr_one:      assert property ( (dvr == 8'h01) |-> (quotient == div && remainder == 8'h00) );
  a_div_lt_dvr:   assert property ( (dvr != 8'h00 && div < dvr) |-> (quotient == 8'h00 && remainder == div) );
  a_div_eq_dvr:   assert property ( (dvr != 8'h00 && div == dvr) |-> (quotient == 8'h01 && remainder == 8'h00) );
  a_div_zero:     assert property ( (dvr != 8'h00 && div == 8'h00) |-> (quotient == 8'h00 && remainder == 8'h00) );

  // Coverage (exercise key scenarios)
  c_div0:         cover property (dvr == 8'h00);
  c_dvr_one:      cover property (dvr == 8'h01);
  c_div_lt:       cover property (dvr != 8'h00 && div < dvr);
  c_div_eq:       cover property (dvr != 8'h00 && div == dvr);
  c_exact_div:    cover property (dvr != 8'h00 && remainder == 8'h00 && div != 8'h00);
  c_big_q:        cover property (dvr != 8'h00 && quotient == 8'hFF); // occurs when dvr==1 and div==255
  c_edges:        cover property (div == 8'hFF && dvr == 8'hFE);
  c_div_is_zero:  cover property (dvr != 8'h00 && div == 8'h00);

endmodule

bind divider divider_sva u_divider_sva (
  .clk(clk),
  .div(div),
  .dvr(dvr),
  .quotient(quotient),
  .remainder(remainder)
);