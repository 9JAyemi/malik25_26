// SVA for altera_mem_if_ddr3_phy_0001_hr_to_fr
// Bindable, concise, checks capture, invert, muxing, X-checks, and phase-to-input mapping.

module altera_mem_if_ddr3_phy_0001_hr_to_fr_sva
(
  input  logic       clk,
  input  logic       d_h0, d_h1, d_l0, d_l1,
  input  logic       q0, q1,
  input  logic       q_h0, q_h1, q_l0, q_l1, q_l0_neg, q_l1_neg
);

  bit pos_seen, neg_seen;
  initial begin pos_seen = 1'b0; neg_seen = 1'b0; end
  always @(posedge clk) pos_seen <= 1'b1;
  always @(negedge clk) neg_seen <= 1'b1;

  // Posedge captures
  assert property (@(posedge clk) disable iff (!pos_seen)
                   (q_h0 == $past(d_h0)) && (q_l0 == $past(d_l0)) &&
                   (q_h1 == $past(d_h1)) && (q_l1 == $past(d_l1)));

  // Negedge inversion (sample after NBA)
  assert property (@(negedge clk) disable iff (!pos_seen)
                   ##0 ((q_l0_neg == ~q_l0) && (q_l1_neg == ~q_l1)));

  // Output muxing correct on both edges (sample after settle)
  assert property (@(posedge clk or negedge clk) disable iff (!pos_seen || !neg_seen)
                   ##0 ( clk ? ((q0==q_l0_neg) && (q1==q_l1_neg))
                             : ((q0==q_h0)     && (q1==q_h1)) ));

  // Phase-to-input mapping: high phase outputs invert of last d_l*
  assert property (@(posedge clk) disable iff (!pos_seen || !neg_seen)
                   ##0 ( (q0 == ~ $past(d_l0)) && (q1 == ~ $past(d_l1)) ));

  // Phase-to-input mapping: low phase outputs last d_h* (from preceding posedge)
  assert property (@(negedge clk) disable iff (!pos_seen)
                   ##0 ( (q0 == $past(d_h0, 1, posedge clk)) &&
                         (q1 == $past(d_h1, 1, posedge clk)) ));

  // No X/Z once both phases have occurred
  assert property (@(posedge clk or negedge clk) disable iff (!pos_seen || !neg_seen)
                   ##0 (!$isunknown({q0,q1,q_h0,q_h1,q_l0,q_l1,q_l0_neg,q_l1_neg})));

  // Coverage: exercise both phases and both lanes
  cover property (@(posedge clk) pos_seen && neg_seen ##0 (q0 == ~ $past(d_l0)) && (q1 == ~ $past(d_l1)));
  cover property (@(negedge clk) pos_seen            ##0 (q0 == $past(d_h0, 1, posedge clk)) &&
                                                     (q1 == $past(d_h1, 1, posedge clk)));
  // Coverage: mux selects distinct values across phases at least once
  cover property (@(posedge clk) pos_seen && neg_seen ##0 ( (q_h0 != q_l0_neg) || (q_h1 != q_l1_neg) ));

endmodule

bind altera_mem_if_ddr3_phy_0001_hr_to_fr
     altera_mem_if_ddr3_phy_0001_hr_to_fr_sva
     sva ( .clk(clk),
           .d_h0(d_h0), .d_h1(d_h1), .d_l0(d_l0), .d_l1(d_l1),
           .q0(q0), .q1(q1),
           .q_h0(q_h0), .q_h1(q_h1), .q_l0(q_l0), .q_l1(q_l1),
           .q_l0_neg(q_l0_neg), .q_l1_neg(q_l1_neg) );