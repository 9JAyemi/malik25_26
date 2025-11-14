// SVA for glitch_free_mux
// Bind into the DUT; accesses internals directly
module gf_mux_sva #(parameter int n = 4) ();

  // Inside bind scope, DUT signals are visible: clk, sel, sys_clk, cur_clk, prev_clk
  logic init;
  initial init = 1'b0;
  always @(posedge clk[0]) init <= 1'b1;

  default clocking cb @(posedge clk[0]); endclocking

  // Sequential updates
  property p_updates_on_sel;
    init && sel |-> (cur_clk == $past(clk) && prev_clk == $past(cur_clk));
  endproperty
  assert property (p_updates_on_sel);

  property p_hold_when_not_sel;
    init && !sel |-> (cur_clk == $past(cur_clk) && prev_clk == $past(prev_clk));
  endproperty
  assert property (p_hold_when_not_sel);

  // Functional mapping to LSB (match DUT semantics with 2-state compare)
  assert property (init && (cur_clk == prev_clk) |-> (sys_clk === cur_clk[0]));
  assert property (init && (cur_clk != prev_clk) |-> (sys_clk === prev_clk[0]));

  // Glitch-free: output edges only coincide with clk[0] posedges
  assert property (@(posedge sys_clk) init |-> $rose(clk[0]));
  assert property (@(negedge sys_clk) init |-> $rose(clk[0]));

  // Stability when no update requested
  assert property (init && !sel |-> $stable(sys_clk));

  // No X on output once both sources are known
  assert property (init && !$isunknown(cur_clk) && !$isunknown(prev_clk) |-> !$isunknown(sys_clk));

  // Coverage
  cover property (sel);
  cover property (sel && (cur_clk == prev_clk));
  cover property (sel && (cur_clk != prev_clk));
  cover property (@(posedge sys_clk) 1);
  cover property (@(negedge sys_clk) 1);
  cover property (sel ##1 sel);

endmodule

bind glitch_free_mux gf_mux_sva #(.n(n)) gf_mux_sva_i ();