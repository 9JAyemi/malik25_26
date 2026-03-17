module up_down_counter_sva (
    input logic       clk,
    input logic       reset,
    input logic       direction,
    input logic [3:0] count
);

    // Reset drives the counter to zero.
    check_reset_clears_count: assert property (
        @(posedge clk) reset |=> (count == 4'b0000)
    );

    // In up mode, 15 wraps to 0.
    check_up_wrap_from_max: assert property (
        @(posedge clk) disable iff (reset)
        direction && (count == 4'b1111) |=> (count == 4'b0000)
    );

    // In up mode, values below 15 increment by 1.
    check_up_increment: assert property (
        @(posedge clk) disable iff (reset)
        direction && (count != 4'b1111) |=> (count == ($past(count) + 4'd1))
    );

    // In down mode, 0 wraps to 15.
    check_down_wrap_from_zero: assert property (
        @(posedge clk) disable iff (reset)
        !direction && (count == 4'b0000) |=> (count == 4'b1111)
    );

    // In down mode, values above 0 decrement by 1.
    check_down_decrement: assert property (
        @(posedge clk) disable iff (reset)
        !direction && (count != 4'b0000) |=> (count == ($past(count) - 4'd1))
    );

endmodule