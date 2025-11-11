// SVA for DeBouncer
// Quality-focused, concise checks and coverage.
// Bind into the DUT to access internal signals.

module DeBouncer_sva #(parameter N = 23) (
  input  logic               clk,
  input  logic               n_reset,
  input  logic               button_in,
  input  logic               DB_out,
  input  logic [N-1:0]       q_reg,
  input  logic               DFF1,
  input  logic               DFF2,
  input  logic               q_add,
  input  logic               q_reset
);

  // 1) Reset behavior (synchronous, active-high)
  // On a reset cycle, internal state clears to 0 next cycle.
  assert property (@(posedge clk) n_reset |=> (DFF1==1'b0 && DFF2==1'b0 && q_reg=='0))
    else $error("Reset did not clear internal state");

  // 2) Combinational tie-offs are consistent
  assert property (@(posedge clk) (q_add == ~q_reg[N-1]))
    else $error("q_add mismatch");
  assert property (@(posedge clk) (q_reset == (DFF1 ^ DFF2)))
    else $error("q_reset mismatch");

  // 3) Synchronizer sampling (when not in reset)
  assert property (@(posedge clk) disable iff (n_reset) DFF1 == $past(button_in))
    else $error("DFF1 did not sample button_in");
  assert property (@(posedge clk) disable iff (n_reset) DFF2 == $past(DFF1))
    else $error("DFF2 did not sample DFF1");

  // 4) Counter next-state behavior (use previous-cycle controls)
  // Increment when stable and not saturated
  assert property (@(posedge clk) disable iff (n_reset)
                   ($past(q_reset)==1'b0 && $past(q_add)==1'b1) |-> (q_reg == $past(q_reg)+1))
    else $error("Counter should increment under stable input");
  // Hold when saturated and stable
  assert property (@(posedge clk) disable iff (n_reset)
                   ($past(q_reset)==1'b0 && $past(q_add)==1'b0) |-> (q_reg == $past(q_reg)))
    else $error("Counter should hold when saturated");
  // Clear on any detected input change
  assert property (@(posedge clk) disable iff (n_reset)
                   ($past(q_reset)==1'b1) |-> (q_reg == '0))
    else $error("Counter should clear on input change");

  // 5) Saturation implies no further increment
  assert property (@(posedge clk) disable iff (n_reset)
                   ($past(q_reg[N-1]) && $past(q_reset)==1'b0) |-> (q_reg == $past(q_reg)))
    else $error("Counter changed after saturation without input change");

  // 6) Debounced output behavior
  // Output must not change while counter MSB was 0
  assert property (@(posedge clk) disable iff (n_reset)
                   ($past(q_reg[N-1])==1'b0) |-> (DB_out == $past(DB_out)))
    else $error("DB_out changed before debounce complete");
  // When MSB was 1, DB_out updates to DFF2
  assert property (@(posedge clk) disable iff (n_reset)
                   ($past(q_reg[N-1])==1'b1) |-> (DB_out == $past(DFF2)))
    else $error("DB_out did not follow DFF2 at saturation");
  // Any DB_out change must be caused by a saturated update to DFF2
  assert property (@(posedge clk) disable iff (n_reset)
                   (DB_out != $past(DB_out)) |-> ($past(q_reg[N-1]) && DB_out == $past(DFF2)))
    else $error("DB_out changed without debounce completion");

  // 7) No X/Z on internal state during operation
  assert property (@(posedge clk) disable iff (n_reset) !$isunknown({DFF1,DFF2,q_reg,DB_out}))
    else $error("Unknown state detected during operation");

  // 8) Coverage
  // Reset seen then operation resumes
  cover property (@(posedge clk) n_reset ##1 !n_reset);
  // Rising debounced transition: DFF2 rises, later counter saturates, then DB_out rises
  cover property (@(posedge clk) disable iff (n_reset)
                  $rose(DFF2) ##[1:$] q_reg[N-1] ##1 (DB_out==1));
  // Falling debounced transition: DFF2 falls, later counter saturates, then DB_out falls
  cover property (@(posedge clk) disable iff (n_reset)
                  $fell(DFF2) ##[1:$] q_reg[N-1] ##1 (DB_out==0));
  // Bounce scenario: input change causes counter clear at least twice before saturation
  cover property (@(posedge clk) disable iff (n_reset)
                  ($rose(q_reset) or $fell(q_reset)) ##[1:$] ($rose(q_reset) or $fell(q_reset)) ##[1:$] q_reg[N-1]);

endmodule

bind DeBouncer DeBouncer_sva #(.N(N)) debouncer_sva_i (
  .clk      (clk),
  .n_reset  (n_reset),
  .button_in(button_in),
  .DB_out   (DB_out),
  .q_reg    (q_reg),
  .DFF1     (DFF1),
  .DFF2     (DFF2),
  .q_add    (q_add),
  .q_reset  (q_reset)
);