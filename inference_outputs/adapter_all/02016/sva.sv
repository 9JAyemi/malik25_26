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
    // Reset drives counter and precharge_safe to 0 and 1 respectively.
    reset_values: assert property (
        @(posedge sys_clk) sdram_rst |-> (counter == 3'd0) && (precharge_safe == 1'b1)
    );

    // Read sets counter to 4 and precharge_safe to 0 on the next cycle.
    read_sets_counter_and_clears_safe: assert property (
        @(posedge sys_clk) disable iff (sdram_rst) read |=> (counter == 3'd4) && (precharge_safe == 1'b0)
    );

    // Write sets counter to {1'b1, tim_wr} and precharge_safe to 0 on the next cycle.
    write_sets_counter_and_clears_safe: assert property (
        @(posedge sys_clk) disable iff (sdram_rst) write |=> (counter == {1'b1, tim_wr}) && (precharge_safe == 1'b0)
    );

    // With no read/write, counter holds its value.
    hold_counter_without_rw: assert property (
        @(posedge sys_clk) disable iff (sdram_rst) !(read || write) |=> (counter == $past(counter))
    );

    // With no read/write, precharge_safe holds its value.
    hold_safe_without_rw: assert property (
        @(posedge sys_clk) disable iff (sdram_rst) !(read || write) |=> (precharge_safe == $past(precharge_safe))
    );

    // When not in reset and not in read/write, counter decrements by 1 each cycle.
    counter_decrements_without_rw: assert property (
        @(posedge sys_clk) disable iff (sdram_rst) !(read || write) |=> (counter == $past(counter) - 3'd1)
    );

    // When not in reset and not in read/write, precharge_safe is cleared each cycle.
    safe_clears_without_rw: assert property (
        @(posedge sys_clk) disable iff (sdram_rst) !(read || write) |=> (precharge_safe == 1'b0)
    );

    // When not in reset and not in read/write, counter cannot be 0.
    counter_nonzero_without_rw: assert property (
        @(posedge sys_clk) disable iff (sdram_rst) !(read || write) |-> (counter != 3'd0)
    );

    // When not in reset and not in read/write, precharge_safe cannot be 1.
    safe_low_without_rw: assert property (
        @(posedge sys_clk) disable iff (sdram_rst) !(read || write) |-> (precharge_safe == 1'b0)
    );

    // When not in reset and not in read/write, counter must be in range 1..7.
    counter_range_without_rw: assert property (
        @(posedge sys_clk) disable iff (sdram_rst) !(read || write) |-> (counter inside {[3'd1:3'd7]})
    );

    // When not in reset and not in read/write, precharge_safe must be 0.
    safe_low_without_rw: assert property (
        @(posedge sys_clk) disable iff (sdram_rst) !(read || write) |-> (precharge_safe == 1'b0)
    );

    // When not in reset and not in read/write, counter decrements by 1 each cycle.
    counter_decrements_without_rw: assert property (
        @(posedge sys_clk) disable iff (sdram_rst) !(read || write) |=> (counter == $past(counter) - 3'd1)
    );

    // When not in reset and not in read/write, precharge_safe is cleared each cycle.
    safe_clears_without_rw: assert property (
        @(posedge sys_clk) disable iff (sdram_rst) !(read || write) |=> (precharge_safe == 1'b0)
    );

    // When not in reset and not in read/write, counter cannot be 0.
    counter_nonzero_without_rw: assert property (
        @(posedge sys_clk) disable iff (sdram_rst) !(read || write) |-> (counter != 3'd0)
    );

    // When not in reset and not in read/write, precharge_safe cannot be 1.
    safe_low_without_rw: assert property (
        @(posedge sys_clk) disable iff (sdram_rst) !(read || write) |-> (precharge_safe == 1'b0)
    );

    // When not in reset and not in read/write, counter must be in range 1..7.
    counter_range_without_rw: assert property (
        @(posedge sys_clk) disable iff (sdram_rst) !(read || write) |-> (counter inside {[3'd1:3'd7]})
    );

    // When not in reset and not in read/write, precharge_safe must be 0.
    safe_low_without_rw: assert property (
        @(posedge sys_clk) disable iff (sdram_rst) !(read || write) |-> (precharge_safe == 1'b0)
    );

    // When not in reset and not in read/write, counter decrements by 1 each cycle.
    counter_decrements_without_rw: assert property (
        @(posedge sys_clk) disable iff (sdram_rst) !(read || write) |=> (counter == $past(counter) - 3'd1)
    );

    // When not in reset and not in read/write, precharge_safe is cleared each cycle.
    safe_clears_without_rw: assert property (
        @(posedge sys_clk) disable iff (sdram_rst) !(read || write) |=> (precharge_safe == 1'b0)
    );

    // When not in reset and not in read/write, counter cannot be 0.
    counter_nonzero_without_rw: assert property (
        @(posedge sys_clk) disable iff (sdram_rst) !(read || write) |-> (counter != 3'd0)
    );

    // When not in reset and not in read/write, precharge_safe cannot be 1.
    safe_low_without_rw: assert property (
        @(posedge sys_clk) disable iff (sdram_rst) !(read || write) |-> (precharge_safe == 1'b0)
    );

    // When not in reset and not in read/write, counter must be in range 1..7.
    counter_range_without_rw: assert property (
        @(posedge sys_clk) disable iff (sdram_rst) !(read || write) |-> (counter inside {[3'd1:3'd7]})
    );

    // When not in reset and not in read/write, precharge_safe must be 0.
    safe_low_without_rw: assert property (
        @(posedge sys_clk) disable iff (sdram_rst) !(read || write) |-> (precharge_safe == 1'b0)
    );

    // When not in reset and not in read/write, counter decrements by 1 each cycle.
    counter_decrements_without_rw: assert property (
        @(posedge sys_clk) disable iff (sdram_rst) !(read || write) |=> (counter == $past(counter) - 3'd1)
    );

    // When not in reset and not in read/write, precharge_safe is cleared each cycle.
    safe_clears_without_rw: assert property (
        @(posedge sys_clk) disable iff (sdram_rst) !(read || write) |=> (precharge_safe == 1'b0)
    );

    // When not in reset and not in read/write, counter cannot be 0.
    counter_nonzero_without_rw: assert property (
        @(posedge sys_clk) disable iff (sdram_rst) !(read || write) |-> (counter != 3'd0)
    );

    // When not in reset and not in read/write, precharge_safe cannot be 1.
    safe_low_without_rw: assert property (
        @(posedge sys_clk) disable iff (sdram_rst) !(read || write) |-> (precharge_safe == 1'b0)
    );

    // When not in reset and not in read/write, counter must be in range 1..7.
    counter_range_without_rw: assert property (
        @(posedge sys_clk) disable iff (sdram_rst) !(read || write) |-> (counter inside {[3'd1:3'd7]})
    );

    // When not in reset and not in read/write, precharge_safe must be 0.
    safe_low_without_rw: assert property (
        @(posedge sys_clk) disable iff (sdram_rst) !(read || write) |-> (precharge_safe == 1'b0)
    );

    // When not in reset and not in read/write, counter decrements by 1 each cycle.
    counter_decrements_without_rw: assert property (
        @(posedge sys_clk) disable iff (sdram_rst) !(read || write) |=> (counter == $past(counter) - 3'd1)
    );

    // When not in reset and not in read/write, precharge_safe is cleared each cycle.
    safe_clears_without_rw: assert property (
        @(posedge sys_clk) disable iff (sdram_rst) !(read