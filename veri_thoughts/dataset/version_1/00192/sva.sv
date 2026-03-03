// SVA for oh_iddr: concise, high-quality checks and coverage
module oh_iddr_sva #(parameter DW=1)
(
  input              clk,
  input              ce,
  input  [DW-1:0]    din,
  input  [DW-1:0]    q1,
  input  [DW-1:0]    q2,
  input  [DW-1:0]    q1_sl, // internal
  input  [DW-1:0]    q2_sh  // internal
);

  // Simple init guards (no reset in DUT)
  logic started_p, started_n;
  initial begin started_p = 1'b0; started_n = 1'b0; end
  always @(posedge clk)  started_p <= 1'b1;
  always @(negedge clk)  started_n <= 1'b1;

  // q1 path: 1-cycle latency, gated by ce on posedge
  // New q1 equals previous q1_sl; functionally equals prev din when prev ce=1, else holds
  assert property (@(posedge clk) disable iff (!started_p)
                   ##0 (q1 == $past(q1_sl)))
    else $error("q1 must equal pre-posedge q1_sl");

  assert property (@(posedge clk) disable iff (!started_p)
                   ##0 (q1 == ($past(ce) ? $past(din) : $past(q1))))
    else $error("q1 functional update/hold mismatch");

  // q1_sl capture on posedge (NBA): update when ce, else hold
  assert property (@(posedge clk) disable iff (!started_p)
                   ##0 (q1_sl == ($past(ce) ? $past(din) : $past(q1_sl))))
    else $error("q1_sl capture/hold mismatch");

  // q2 path: half-cycle latency from negedge, no gating
  // New q2 equals q2_sh at this posedge and equals din from last negedge
  assert property (@(posedge clk) disable iff (!started_p)
                   ##0 (q2 == q2_sh))
    else $error("q2 must equal q2_sh at posedge");

  assert property (@(posedge clk) disable iff (!started_n)
                   ##0 (q2 == $past(din, 1, negedge clk)))
    else $error("q2 must equal din captured on the last negedge");

  // q2_sh capture on negedge (NBA)
  assert property (@(negedge clk) disable iff (!started_n)
                   ##0 (q2_sh == din))
    else $error("q2_sh must capture din on negedge");

  // Minimal targeted coverage
  // q1 updates when ce was 1
  cover property (@(posedge clk) disable iff (!started_p)
                  $past(ce) ##0 $changed(q1));

  // q1 holds when ce was 0
  cover property (@(posedge clk) disable iff (!started_p)
                  !$past(ce) ##0 $stable(q1));

  // q2 changes due to negedge capture
  cover property (@(posedge clk) disable iff (!started_n)
                  ##0 $changed(q2));

  // Independent behavior: q2 changes while q1 holds (ce=0)
  cover property (@(posedge clk) disable iff (!started_p || !started_n)
                  !$past(ce) ##0 ($stable(q1) && $changed(q2)));

  // Both paths change in same posedge (edge activity on both halves)
  cover property (@(posedge clk) disable iff (!started_p || !started_n)
                  $past(ce) ##0 ($changed(q1) && $changed(q2)));

endmodule

// Bind into DUT (accesses internal q1_sl/q2_sh)
bind oh_iddr oh_iddr_sva #(.DW(DW)) oh_iddr_sva_i (.*);