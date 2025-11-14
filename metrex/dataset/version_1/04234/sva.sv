// SVA for my_delayed_clk
// Bind this checker to the DUT
bind my_delayed_clk my_delayed_clk_sva #(.DELAY_CYCLES(DELAY_CYCLES)) u_sva ();

module my_delayed_clk_sva #(parameter int DELAY_CYCLES = 10) ();

  // Access DUT scope directly (bind inserts this module into DUT scope)
  // Signals in DUT scope: GCLK, GATE, CLK, VPWR, VGND, RST, delay_counter, delayed_clk

  // Default clocking and disable conditions
  default clocking cb @(posedge CLK); endclocking
  default disable iff (!RST || VPWR !== 1'b1 || VGND !== 1'b0);

  // Past-valid guard for $past()
  bit past_valid;
  initial past_valid = 1'b0;
  always_ff @(posedge CLK) past_valid <= 1'b1;

  // Power rails should be good (assume/assert as environment constraint)
  assume property (@(posedge CLK) VPWR === 1'b1 && VGND === 1'b0);

  // While in reset, state is cleared
  assert property (@(posedge CLK) !RST |-> (delay_counter == '0 && delayed_clk == 1'b0 && GCLK == 1'b0));

  // No X/Z on key signals when enabled
  assert property (past_valid |-> !$isunknown({RST, GATE, GCLK, delayed_clk, delay_counter}));

  // Counter behavior
  // - increments by 1 when GATE=1
  assert property (past_valid && GATE |-> delay_counter == $past(delay_counter) + {{(DELAY_CYCLES-1){1'b0}},1'b1});
  // - holds when GATE=0
  assert property (past_valid && !GATE |-> delay_counter == $past(delay_counter));

  // delayed_clk next-state function:
  // - if previous cycle had GATE=1, delayed_clk equals (delay_counter == DELAY_CYCLES-1) from prev cycle
  // - else it holds its value
  assert property (past_valid |->
                   delayed_clk == ($past(GATE)
                                   ? ($past(delay_counter) == (DELAY_CYCLES-1))
                                   : $past(delayed_clk)));

  // GCLK is a one-cycle pipeline of delayed_clk
  assert property (past_valid |-> GCLK == $past(delayed_clk));

  // If the pulse is generated and GATE stays high, the pulse is exactly 1 cycle wide
  assert property (past_valid && delayed_clk && GATE |-> ##1 !delayed_clk);

  // Coverage: typical delayed pulse then GCLK follows
  cover property (past_valid && RST && GATE[*DELAY_CYCLES] ##1 delayed_clk ##1 GCLK);

  // Coverage: gate-low holds state
  cover property (past_valid && RST && !GATE ##1 $stable(delay_counter) && $stable(delayed_clk));

endmodule