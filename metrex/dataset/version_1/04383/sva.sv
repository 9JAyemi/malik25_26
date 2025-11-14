// SVA for dff_keep_5_new
module dff_keep_5_new_sva (input clk, input [4:0] d, input [4:0] q);
  default clocking cb @(posedge clk); endclocking

  // 1-cycle DFF behavior
  a_reg: assert property ( $past(1'b1) |-> (q == $past(d)) );

  // Output only updates on posedge (stable at negedge)
  a_no_negedge_update: assert property (@(negedge clk) $stable(q));

  // No new Xs introduced: if past D known then Q known
  a_no_new_x: assert property ( $past(1'b1) && !$isunknown($past(d)) |-> !$isunknown(q) );

  // Q matches internal register (bound in DUT scope)
  a_q_eq_qreg: assert property (q == q_reg);

  // Coverage
  c_cap_change: cover property ( $past(1'b1) && $changed(d) && (q == $past(d)) );
  c_hold:       cover property ( $past(1'b1) && (d == $past(d)) && (q == $past(d)) );

  genvar i;
  generate
    for (i = 0; i < 5; i++) begin : bit_cov
      c_bit_0to1: cover property ( $past(1'b1) && !$past(d[i]) &&  d[i] );
      c_bit_1to0: cover property ( $past(1'b1) &&  $past(d[i]) && !d[i] );
    end
  endgenerate
endmodule

bind dff_keep_5_new dff_keep_5_new_sva u_dff_keep_5_new_sva (.clk(clk), .d(d), .q(q));