// SVA for posedge_D_ff_with_enable
module posedge_D_ff_with_enable_sva(input logic clk, d, en, q);

  // Track when $past is valid
  logic past_valid;
  initial past_valid = 1'b0;
  always @(posedge clk) past_valid <= 1'b1;

  default clocking cb @ (posedge clk); endclocking

  // Enable must toggle only when clk is low (glitch-free clock gating)
  property en_changes_only_when_clk_low;
    @(posedge en or negedge en) !clk;
  endproperty
  assert property (en_changes_only_when_clk_low);

  // On enabled clock edge, q captures d (post-NBA)
  property capture_correct;
    disable iff (!past_valid)
    en |-> ##0 (q == $past(d));
  endproperty
  assert property (capture_correct);

  // When disabled, q must hold value across clk edges
  property hold_when_disabled;
    disable iff (!past_valid)
    !en |-> ##0 $stable(q);
  endproperty
  assert property (hold_when_disabled);

  // q can only change coincident with a rising clk and en=1
  property q_changes_only_on_clk_edge;
    @(posedge q or negedge q) $rose(clk) && en;
  endproperty
  assert property (q_changes_only_on_clk_edge);

  // X-checks on control/data at capture
  assert property (disable iff (!past_valid) !$isunknown(en));
  assert property (disable iff (!past_valid) en |-> !$isunknown(d));
  assert property (disable iff (!past_valid) en |-> ##0 !$isunknown(q));

  // Functional coverage
  cover property (en);                                 // enable path exercised
  cover property (!en);                                // hold path exercised
  cover property (en && (d==1'b0) ##0 (q==1'b0));      // capture 0
  cover property (en && (d==1'b1) ##0 (q==1'b1));      // capture 1
  cover property (@(posedge en) !clk);                 // legal enable rise
  cover property (@(negedge en) !clk);                 // legal enable fall

endmodule

bind posedge_D_ff_with_enable posedge_D_ff_with_enable_sva sva_i(.clk(clk), .d(d), .en(en), .q(q));