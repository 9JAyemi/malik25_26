module register_sva (
    input logic clk,
    input logic rst,
    input logic [7:0] data_in,
    input logic enable,
    input logic [7:0] data_out
);
    // Clock: clk; Reset: rst (active-high, synchronous)
    // Behavior: sequential register with enable; data_out mirrors stored_data combinationally

    // On reset, output becomes 0 on the next cycle.
    reset_clears_output: assert property (
        @(posedge clk) rst |=> (data_out == 8'h00)
    );

    // With enable HIGH (and not in reset), next cycle output equals previous data_in.
    write_updates_output: assert property (
        @(posedge clk) disable iff (rst) enable |=> (data_out == $past(data_in))
    );

    // With enable LOW (and not in reset), next cycle output holds its value.
    hold_when_enable_low: assert property (
        @(posedge clk) disable iff (rst) !enable |=> (data_out == $past(data_out))
    );

    // Output changes only if there was an enable or reset in the prior cycle.
    change_requires_write_or_reset: assert property (
        @(posedge clk) disable iff (rst) $changed(data_out) |-> ($past(enable) || $past(rst))
    );

    // Two back-to-back enables: at the second-next cycle, output equals data_in from the prior cycle.
    two_writes_in_sequence: assert property (
        @(posedge clk) disable iff (rst) (enable ##1 enable) |=> (data_out == $past(data_in, 1))
    );

    // Two cycles with enable LOW: output equals the value from two cycles earlier.
    hold_two_cycles_no_enable: assert property (
        @(posedge clk) disable iff (rst) (!enable ##1 !enable) |=> (data_out == $past(data_out, 2))
    );

    // If data_in changes while enable is LOW, output still holds on the next cycle.
    hold_despite_input_change: assert property (
        @(posedge clk) disable iff (rst) (!enable && $changed(data_in)) |=> (data_out == $past(data_out))
    );

    // After reset deasserts and no write that cycle, output remains 0 on the next cycle.
    deassert_reset_no_write_keeps_zero: assert property (
        @(posedge clk) ($fell(rst) && !enable) |=> (data_out == 8'h00)
    );

    // After a write, the written value holds until the next write (reset aborts the check).
    hold_after_write_until_next_write: assert property (
        @(posedge clk) disable iff (rst) enable |=> (data_out == $past(data_in)) until_with (enable)
    );

    // Reset dominates enable: if both are HIGH, next cycle output is 0.
    reset_overrides_enable: assert property (
        @(posedge clk) (rst && enable) |=> (data_out == 8'h00)
    );
endmodule