// SVA for timer. Bind this to the DUT.
// Notes:
// - timer_count_done is level-sticky while timer_enable=1 per RTL
// - Equality is evaluated on the pre-increment value (done asserted same cycle, counter cleared next)

module timer_sva (
  input logic         clk,
  input logic         reset,
  input logic [31:0]  timer_count,
  input logic         timer_enable,
  input logic         timer_interrupt_clear,
  input logic         timer_count_done,
  input logic         timer_interrupt,
  input logic [31:0]  timer_count_running
);

  default clocking cb @(posedge clk); endclocking
  default disable iff (reset)

  // Synchronous reset drives all regs low (checked in-cycle of reset)
  assert property (@(posedge clk) reset |-> (timer_count_running==32'd0 && !timer_count_done && !timer_interrupt));

  // When disabled, counter and done clear in the same cycle
  assert property (!timer_enable |-> (timer_count_running==32'd0 && !timer_count_done));

  // While enabled and no hit, counter increments by 1 on the next cycle
  assert property (timer_enable && (timer_count_running != timer_count)
                   |=> timer_count_running == $past(timer_count_running)+1);

  // Hit behavior: done goes high same cycle; counter clears next cycle
  assert property (timer_enable && (timer_count_running == timer_count) |-> timer_count_done);
  assert property (timer_enable && (timer_count_running == timer_count) |=> timer_count_running==32'd0);

  // Done can only rise on a hit under enable
  assert property ($rose(timer_count_done)
                   |-> $past(timer_enable) && ($past(timer_count_running) == $past(timer_count)));

  // Done remains 1 while enable stays 1 (sticky)
  assert property (timer_enable && $past(timer_enable) && $past(timer_count_done) |-> timer_count_done);

  // Interrupt clear dominates in-cycle
  assert property (timer_interrupt_clear |-> !timer_interrupt);

  // Interrupt sets in-cycle when done is 1 and not cleared
  assert property (!timer_interrupt_clear && timer_count_done |-> timer_interrupt);

  // If neither cleared nor (re)set, interrupt holds value
  assert property (!timer_interrupt_clear && !timer_count_done
                   |=> timer_interrupt == $past(timer_interrupt));

  // Interrupt can only rise if previously not cleared and done was 1
  assert property ($rose(timer_interrupt) |-> $past(timer_count_done) && !$past(timer_interrupt_clear));

  // Basic X checks on outputs
  assert property (!$isunknown(timer_count_done) && !$isunknown(timer_interrupt));

  // ---------------- Coverage ----------------

  // Observe a hit
  cover property (timer_enable && (timer_count_running == timer_count) && timer_count_done);

  // Zero-count immediate hit and interrupt set
  cover property ($rose(timer_enable) && (timer_count==32'd0)
                  ##0 timer_count_done && timer_interrupt);

  // Interrupt lifecycle: set -> clear -> re-set (while done remains 1)
  cover property (timer_count_done && timer_interrupt
                  ##1 timer_interrupt_clear && !timer_interrupt
                  ##1 !timer_interrupt_clear && timer_count_done && timer_interrupt);

  // Disable clears counter and done
  cover property ($rose(timer_enable) ##1 !timer_enable ##0 (timer_count_running==32'd0 && !timer_count_done));

endmodule

// Bind into DUT (connects to internal counter as well)
bind timer timer_sva u_timer_sva (
  .clk                  (clk),
  .reset                (reset),
  .timer_count          (timer_count),
  .timer_enable         (timer_enable),
  .timer_interrupt_clear(timer_interrupt_clear),
  .timer_count_done     (timer_count_done),
  .timer_interrupt      (timer_interrupt),
  .timer_count_running  (timer_count_running)
);