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

// Reset clears the counter and sets precharge_safe high.
    check_reset_clears_state: assert property (
        @(posedge sys_clk) sdram_rst |=> (counter == 3'd0) && (precharge_safe == 1'b1)
    );

// A read sets the counter to 4 and clears precharge_safe.
    check_read_sets_counter_and_clears_safe: assert property (
        @(posedge sys_clk) disable iff (sdram_rst)
        read |=> (counter == 3'd4) && (precharge_safe == 1'b0)
    );

// A write with tim_wr==0 sets the counter to 3 and clears precharge_safe.
    check_write_zero_sets_counter_and_clears_safe: assert property (
        @(posedge sys_clk) disable iff (sdram_rst)
        (write && (tim_wr == 2'd0)) |=> (counter == 3'd3) && (precharge_safe == 1'b0)
    );

// A write with tim_wr==1 sets the counter to 2 and clears precharge_safe.
    check_write_one_sets_counter_and_clears_safe: assert property (
        @(posedge sys_clk) disable iff (sdram_rst)
        (write && (tim_wr == 2'd1)) |=> (counter == 3'd2) && (precharge_safe == 1'b0)
    );

// A write with tim_wr==2 sets the counter to 1 and clears precharge_safe.
    check_write_two_sets_counter_and_clears_safe: assert property (
        @(posedge sys_clk) disable iff (sdram_rst)
        (write && (tim_wr == 2'd2)) |=> (counter == 3'd1) && (precharge_safe == 1'b0)
    );

// A write with tim_wr==3 sets the counter to 0 and clears precharge_safe.
    check_write_three_sets_counter_and_clears_safe: assert property (
        @(posedge sys_clk) disable iff (sdram_rst)
        (write && (tim_wr == 2'd3)) |=> (counter == 3'd0) && (precharge_safe == 1'b0)
    );

// Without read or write, a counter value of 1 sets precharge_safe high.
    check_counter_one_sets_safe: assert property (
        @(posedge sys_clk) disable iff (sdram_rst)
        (!read && !write && (counter == 3'd1)) |=> (precharge_safe == 1'b1)
    );

// Without read or write, a counter value other than 1 keeps precharge_safe low.
    check_counter_not_one_keeps_safe_low: assert property (
        @(posedge sys_clk) disable iff (sdram_rst)
        (!read && !write && (counter != 3'd1)) |=> (precharge_safe == 1'b0)
    );

// Without read or write, a low precharge_safe decrements the counter by one.
    check_counter_decrements_when_safe_low: assert property (
        @(posedge sys_clk) disable iff (sdram_rst)
        (!read && !write && (precharge_safe == 1'b0)) |=> (counter == ($past(counter) - 3'd1))
    );

// Without read or write, a high precharge_safe leaves the counter unchanged.
    check_counter_holds_when_safe_high: assert property (
        @(posedge sys_clk) disable iff (sdram_rst)
        (!read && !write && (precharge_safe == 1'b1)) |=> (counter == $past(counter))
    );

endmodule
