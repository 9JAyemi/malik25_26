// SVA for oh_iddr: bindable assertion module + bind statement

module oh_iddr_sva #(parameter DW=1)
(
  input                  clk,
  input                  ce,
  input      [DW-1:0]    din,
  input      [DW-1:0]    q1,
  input      [DW-1:0]    q2,
  input      [DW-1:0]    q1_sl,
  input      [DW-1:0]    q2_sh
);

  logic pv_pos, pv_neg;
  initial begin pv_pos = 1'b0; pv_neg = 1'b0; end
  always @(posedge clk)  pv_pos <= 1'b1;
  always @(negedge clk)  pv_neg <= 1'b1;

  // q1 is one-posedge delayed version of q1_sl
  assert property (@(posedge clk) disable iff(!pv_pos)
                   q1 == $past(q1_sl));

  // When ce==1, q1 on next posedge equals din of this posedge
  assert property (@(posedge clk) disable iff(!pv_pos)
                   ce |=> q1 == $past(din));

  // When ce==0, q1 holds across posedges
  assert property (@(posedge clk) disable iff(!pv_pos)
                   !ce |=> q1 == $past(q1));

  // q1_sl captures din only when ce==1; otherwise holds
  assert property (@(posedge clk) disable iff(!pv_pos)
                   ce |=> q1_sl == $past(din));
  assert property (@(posedge clk) disable iff(!pv_pos)
                   !ce |=> q1_sl == $past(q1_sl));

  // q2 equals din sampled at most recent negedge before this posedge
  assert property (@(posedge clk) disable iff(!pv_pos || !pv_neg)
                   q2 == $past(din, 1, negedge clk));

  // Consistency: q2 reflects q2_sh captured at last negedge
  assert property (@(posedge clk) disable iff(!pv_pos || !pv_neg)
                   q2 == $past(q2_sh, 1, negedge clk));

  // Coverage
  cover property (@(posedge clk) pv_pos && ce ##1 (q1 == $past(din)));
  cover property (@(posedge clk) pv_pos && (q2 == $past(din, 1, negedge clk)));
  cover property (@(posedge clk) pv_pos && !ce ##1 (q1 == $past(q1)));

endmodule

// Bind into DUT
bind oh_iddr oh_iddr_sva #(.DW(DW)) oh_iddr_sva_i (
  .clk(clk),
  .ce(ce),
  .din(din),
  .q1(q1),
  .q2(q2),
  .q1_sl(q1_sl),
  .q2_sh(q2_sh)
);