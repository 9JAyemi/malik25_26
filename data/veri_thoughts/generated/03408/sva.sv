module counter_sva (
    input logic       clk,
    input logic       rst,
    input logic       inc,
    input logic       dec,
    input logic [3:0] cnt
);

    // Reset drives the counter to zero.
    check_reset_clears_count: assert property (
        @(posedge clk)
        rst |=> (cnt == 4'd0)
    );

    // A single increment advances the count by one below 15.
    check_increment_advances_count: assert property (
        @(posedge clk) disable iff (rst)
        (inc && !dec && (cnt != 4'd15)) |=> (cnt == ($past(cnt) + 4'd1))
    );

    // Increment wraps from 15 back to 0.
    check_increment_wraps_to_zero: assert property (
        @(posedge clk) disable iff (rst)
        (inc && !dec && (cnt == 4'd15)) |=> (cnt == 4'd0)
    );

    // A single decrement reduces the count by one above 0.
    check_decrement_reduces_count: assert property (
        @(posedge clk) disable iff (rst)
        (dec && !inc && (cnt != 4'd0)) |=> (cnt == ($past(cnt) - 4'd1))
    );

    // Decrement wraps from 0 back to 15.
    check_decrement_wraps_to_max: assert property (
        @(posedge clk) disable iff (rst)
        (dec && !inc && (cnt == 4'd0)) |=> (cnt == 4'd15)
    );

    // With no increment or decrement, the count holds.
    check_hold_when_idle: assert property (
        @(posedge clk) disable iff (rst)
        (!inc && !dec) |=> (cnt == $past(cnt))
    );

    // With increment and decrement both high, the count holds.
    check_hold_when_both_asserted: assert property (
        @(posedge clk) disable iff (rst)
        (inc && dec) |=> (cnt == $past(cnt))
    );

endmodule