module hpdmc_banktimer_sva (
    input logic sys_clk,
    input logic sdram_rst,
    input logic tim_cas,
    input logic [1:0] tim_wr,
    input logic read,
    input logic write,
    input logic precharge_safe,
    input logic [2:0] counter
);

    ///// Reset behavior /////
    // On synchronous reset, counter=0 and precharge_safe=1 on next cycle.
    reset_sync_values: assert property (
        @(posedge sys_clk) sdram_rst |=> (counter == 3'd0) && (precharge_safe == 1'b1)
    );

    ///// Access load behavior /////
    // A read loads counter to 4 and clears precharge_safe on next cycle.
    on_read_loads_and_clears: assert property (
        @(posedge sys_clk) disable iff (sdram_rst) read |=> (counter == 3'd4) && (precharge_safe == 1'b0)
    );
    // A write (when read is low) loads counter to {1,tim_wr} and clears precharge_safe on next cycle.
    on_write_loads_and_clears: assert property (
        @(posedge sys_clk) disable iff (sdram_rst) (!read && write) |=> (counter == {1'b1, tim_wr}) && (precharge_safe == 1'b0)
    );
    // Read has priority over write when both are asserted.
    read_has_priority_over_write: assert property (
        @(posedge sys_clk) disable iff (sdram_rst) (read && write) |=> (counter == 3'd4) && (precharge_safe == 1'b0)
    );

    ///// Countdown behavior /////
    // While busy and no new access, counter decrements by 1 each cycle.
    decrement_while_busy: assert property (
        @(posedge sys_clk) disable iff (sdram_rst) (!read && !write && (precharge_safe == 1'b0)) |=> (counter == $past(counter) - 3'd1)
    );
    // When counter is 1 and no new access, precharge_safe becomes 1 on next cycle.
    set_safe_when_count_one: assert property (
        @(posedge sys_clk) disable iff (sdram_rst) (!read && !write && (counter == 3'd1)) |=> (precharge_safe == 1'b1)
    );
    // While safe and idle, precharge_safe and counter hold their values.
    hold_while_safe_idle: assert property (
        @(posedge sys_clk) disable iff (sdram_rst) (!read && !write && (precharge_safe == 1'b1)) |=> (precharge_safe == 1'b1) && (counter == $past(counter))
    );
    // While unsafe and counter != 1 with no new access, precharge_safe stays 0.
    stay_unsafe_until_one: assert property (
        @(posedge sys_clk) disable iff (sdram_rst) (!read && !write && (precharge_safe == 1'b0) && (counter != 3'd1)) |=> (precharge_safe == 1'b0)
    );

    ///// Safety edges /////
    // precharge_safe can only fall due to a read or write in the previous cycle.
    fall_requires_access: assert property (
        @(posedge sys_clk) disable iff (sdram_rst) $fell(precharge_safe) |-> $past(read || write)
    );
    // precharge_safe can only rise due to reset or counter==1 without a new access.
    rise_requires_reset_or_count1: assert property (
        @(posedge sys_clk) disable iff (sdram_rst) $rose(precharge_safe) |-> $past(sdram_rst || (!read && !write && (counter == 3'd1)))
    );

    ///// Invariants /////
    // Counter is never 0 while precharge_safe is 0 (no underflow while busy).
    unsafe_never_zero_count: assert property (
        @(posedge sys_clk) disable iff (sdram_rst) (precharge_safe == 1'b0) |-> (counter != 3'd0)
    );
    // After any access, loaded counter MSB is 1.
    after_access_msb_high: assert property (
        @(posedge sys_clk) disable iff (sdram_rst) (read || (!read && write)) |=> (counter[2] == 1'b1)
    );

endmodule