module counter_3bit_sync_reset_sva (
  input logic clk,
  input logic reset,
  input logic ena,
  input logic [2:0] count,
  input logic flag
);

  // While reset is HIGH, outputs must be zero.
  reset_outputs_zero: assert property (
    @(posedge clk) reset |-> (count == 3'b000) && (flag == 1'b0)
  );

  // When disabled, count and flag hold their values.
  hold_when_disabled: assert property (
    @(posedge clk) disable iff (reset) (!ena) |=> (count == $past(count)) && (flag == $past(flag))
  );

  // When enabled and not at max, count increments and flag clears next cycle.
  increment_when_enabled: assert property (
    @(posedge clk) disable iff (reset) (ena && (count != 3'b111)) |=> (count == $past(count) + 3'b001) && (flag == 1'b0)
  );

  // When enabled and at max, wrap to zero and set flag next cycle.
  wrap_and_set_flag: assert property (
    @(posedge clk) disable iff (reset) (ena && (count == 3'b111)) |=> (count == 3'b000) && (flag == 1'b1)
  );

  // Flag high implies count is zero in the same cycle.
  flag_implies_count_zero: assert property (
    @(posedge clk) disable iff (reset) flag |-> (count == 3'b000)
  );

  // Flag can only rise after an enabled wrap from 7.
  flag_rise_on_wrap_only: assert property (
    @(posedge clk) disable iff (reset) $rose(flag) |-> ($past(ena) && ($past(count) == 3'b111))
  );

  // Any change in count must be due to enable in the previous cycle.
  count_change_requires_enable: assert property (
    @(posedge clk) disable iff (reset) ($past(1'b1) && (count != $past(count))) |-> $past(ena)
  );

  // Any change in flag must be due to enable in the previous cycle.
  flag_change_requires_enable: assert property (
    @(posedge clk) disable iff (reset) ($past(1'b1) && (flag != $past(flag))) |-> $past(ena)
  );

  // First enabled cycle after wrap (count=0, flag=1) clears flag and sets count to 1.
  clear_flag_on_enable_from_zero: assert property (
    @(posedge clk) disable iff (reset) (ena && (count == 3'b000) && (flag == 1'b1)) |=> (count == 3'b001) && (flag == 1'b0)
  );

  // When enabled, count must change on the next cycle (increment or wrap).
  enabled_step_changes_count: assert property (
    @(posedge clk) disable iff (reset) ena |=> (count != $past(count))
  );

endmodule