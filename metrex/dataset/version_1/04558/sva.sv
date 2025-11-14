// SVA for dual_edge_triggered_ff
// Bindable, concise, and checks key functional/temporal behavior on both edges.

module dual_edge_triggered_ff_sva (
  input logic clk,
  input logic d,
  input logic q,
  input logic d1, d2,
  input logic q1, q2
);
  // Start gating to avoid first-cycle $past issues (no reset in DUT)
  bit seen_pos, seen_neg, started;
  initial begin seen_pos = 0; seen_neg = 0; started = 0; end
  always @(posedge clk) begin seen_pos <= 1; if (seen_neg) started <= 1; end
  always @(negedge clk) begin seen_neg <= 1; if (seen_pos) started <= 1; end

  // Combinational output mapping
  a_q_is_q2: assert property (@(posedge clk or negedge clk) disable iff (!started) q == q2);

  // Stage-1 posedge captures (checked from the following negedge)
  a_d1_pos_cap: assert property (@(negedge clk) disable iff (!started)
                                 $past(d1, 0, posedge clk) == $past(d, 0, posedge clk));
  a_q1_pos_cap: assert property (@(negedge clk) disable iff (!started)
                                 $past(q1, 0, posedge clk) == $past(q2, 0, posedge clk));

  // Stage-2 negedge captures/updates
  a_d2_neg_cap: assert property (@(negedge clk) disable iff (!started)
                                 d2 == $past(q1, 0, posedge clk));
  a_q2_neg_xor: assert property (@(negedge clk) disable iff (!started)
                                 q2 == ($past(d, 0, posedge clk) ^ $past(q2, 0, posedge clk)));

  // Edge-discipline: signals only update on their intended edge
  a_q2_stable_on_pos: assert property (@(posedge clk) disable iff (!started) $stable(q2));
  a_d2_stable_on_pos: assert property (@(posedge clk) disable iff (!started) $stable(d2));
  a_d1_stable_on_neg: assert property (@(negedge clk) disable iff (!started) $stable(d1));
  a_q1_stable_on_neg: assert property (@(negedge clk) disable iff (!started) $stable(q1));
  a_q_stable_on_pos:  assert property (@(posedge clk) disable iff (!started) $stable(q));

  // X/Z hygiene at sampling edges
  a_no_x_pos: assert property (@(posedge clk) disable iff (!started)
                               !$isunknown({d, q2, q1, d1, q}));
  a_no_x_neg: assert property (@(negedge clk) disable iff (!started)
                               !$isunknown({q1, d1, d2, q2, q}));

  // Functional coverage
  c_both_edges_pos: cover property (@(posedge clk) 1);
  c_both_edges_neg: cover property (@(negedge clk) 1);
  c_q2_toggles_when_d1: cover property (@(negedge clk)
                             ($past(d, 0, posedge clk) == 1) && (q2 != $past(q2, 0, posedge clk)));
  c_q2_holds_when_d0:   cover property (@(negedge clk)
                             ($past(d, 0, posedge clk) == 0) && (q2 == $past(q2, 0, posedge clk)));
endmodule

// Bind into the DUT (accesses internal regs)
bind dual_edge_triggered_ff dual_edge_triggered_ff_sva
  dual_edge_triggered_ff_sva_i(.clk(clk), .d(d), .q(q), .d1(d1), .d2(d2), .q1(q1), .q2(q2));