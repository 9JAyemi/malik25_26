// SVA for bw_clk_cclk_inv_128x
module bw_clk_cclk_inv_128x_sva (input logic clkin, clkout);

  // Functional equivalence on any change (allowing #0 propagation)
  property p_inverse_rel;
    @(posedge clkin or negedge clkin or posedge clkout or negedge clkout)
      ##0 (clkout === ~clkin);
  endproperty
  a_inverse_rel: assert property (p_inverse_rel);

  // Input edges must cause opposite output edges in the same timestep
  a_in_rise_out_fall: assert property (@(posedge clkin)  ##0 $fell(clkout));
  a_in_fall_out_rise: assert property (@(negedge clkin)  ##0 $rose(clkout));

  // Output edges must correspond to opposite input edges (no spurious output toggles)
  a_out_rise_in_fall: assert property (@(posedge clkout) ##0 $fell(clkin));
  a_out_fall_in_rise: assert property (@(negedge clkout) ##0 $rose(clkin));

  // Coverage: see both edge mappings
  c_in_rise_out_fall: cover property (@(posedge clkin)  ##0 $fell(clkout));
  c_in_fall_out_rise: cover property (@(negedge clkin)  ##0 $rose(clkout));
  c_out_rise_in_fall: cover property (@(posedge clkout) ##0 $fell(clkin));
  c_out_fall_in_rise: cover property (@(negedge clkout) ##0 $rose(clkin));

endmodule

bind bw_clk_cclk_inv_128x bw_clk_cclk_inv_128x_sva (.*);