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

    // Reset clears the counter and raises precharge_safe.
    check_reset_clears_state: assert property (
        @(posedge sys_clk)
        sdram_rst |=> (counter == 3'd0 && precharge_safe == 1'b1)
    );

    // Read sets the counter to 4 and lowers precharge_safe.
    check_read_sets_counter_and_clears_precharge: assert property (
        @(posedge sys_clk) disable iff (sdram_rst)
        read |=> (counter == 3'd4 && precharge_safe == 1'b0)
    );

    // Write sets the counter from tim_wr and lowers precharge_safe.
    check_write_sets_counter_from_tim_wr_and_clears_precharge: assert property (
        @(posedge sys_clk) disable iff (sdram_rst)
        write |=> (counter == {1'b1, tim_wr} && precharge_safe == 1'b0)
    );

    // Without read or write, the counter holds its value.
    check_idle_holds_counter: assert property (
        @(posedge sys_clk) disable iff (sdram_rst)
        (!read && !write) |=> (counter == $past(counter))
    );

    // Without read or write, precharge_safe holds its value.
    check_idle_holds_precharge_safe: assert property (
        @(posedge sys_clk) disable iff (sdram_rst)
        (!read && !write) |=> (precharge_safe == $past(precharge_safe))
    );

    // When not in the 1-state, the counter decrements when precharge_safe is low.
    check_counter_decrements_when_precharge_low: assert property (
        @(posedge sys_clk) disable iff (sdram_rst)
        (!read && !write && (counter != 3'd1) && (precharge_safe == 1'b0)) |=> (counter == ($past(counter) - 3'd1))
    );

    // When not in the 1-state, the counter holds when precharge_safe is high.
    check_counter_holds_when_precharge_high: assert property (
        @(posedge sys_clk) disable iff (sdram_rst)
        (!read && !write && (counter != 3'd1) && (precharge_safe == 1'b1)) |=> (counter == $past(counter))
    );

    // When the counter is 1, precharge_safe is raised on the next cycle.
    check_precharge_safe_set_on_counter_one: assert property (
        @(posedge sys_clk) disable iff (sdram_rst)
        (!read && !write && (counter == 3'd1)) |=> (precharge_safe == 1'b1)
    );

endmodule