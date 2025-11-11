// SVA for dual_edge_triggered_ff
module detff_sva(input logic clk, d, q);

  bit past_valid;
  initial past_valid = 0;
  always @(posedge clk) past_valid <= 1;

  // Rising-edge capture: q equals prior-cycle d
  property p_posedge_capture;
    @(posedge clk) disable iff (!past_valid)
      q == $past(d);
  endproperty
  assert property (p_posedge_capture);

  // No capture on falling edge
  property p_no_falling_edge_capture;
    @(negedge clk) disable iff (!past_valid)
      $stable(q);
  endproperty
  assert property (p_no_falling_edge_capture);

  // Sanity: no X/Z on sampled data and output after first valid sample
  assert property (@(posedge clk) disable iff (!past_valid) !$isunknown(d));
  assert property (@(posedge clk) disable iff (!past_valid) !$isunknown(q));

  // Functional coverage
  cover property (@(posedge clk) disable iff (!past_valid)
                  ($past(q)==0 && d==1 && q==1)); // capture 1
  cover property (@(posedge clk) disable iff (!past_valid)
                  ($past(q)==1 && d==0 && q==0)); // capture 0
  cover property (@(posedge clk) disable iff (!past_valid)
                  (d==$past(q) && q==$past(q)));  // hold

  // Cover at least one falling edge with stability
  cover property (@(negedge clk) disable iff (!past_valid) $stable(q));

endmodule

bind dual_edge_triggered_ff detff_sva detff_sva_i(.clk(clk), .d(d), .q(q));