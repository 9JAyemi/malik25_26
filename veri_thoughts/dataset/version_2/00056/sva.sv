module up_down_counter_sva (
    input logic clk,
    input logic reset,
    input logic mode,
    input logic [3:0] initial_value,
    input logic [3:0] counter_value
);

    // Synchronous reset loads counter_value from initial_value.
    check_reset_load: assert property (
        @(posedge clk) reset |=> counter_value == $past(initial_value)
    );

    // In up mode, non-maximum values increment by one.
    check_up_increment: assert property (
        @(posedge clk) disable iff (reset)
        (mode == 1'b0 && counter_value != 4'b1111) |=> counter_value == ($past(counter_value) + 4'd1)
    );

    // In up mode, 15 wraps to 0.
    check_up_wrap: assert property (
        @(posedge clk) disable iff (reset)
        (mode == 1'b0 && counter_value == 4'b1111) |=> counter_value == 4'b0000
    );

    // In down mode, non-zero values decrement by one.
    check_down_decrement: assert property (
        @(posedge clk) disable iff (reset)
        (mode == 1'b1 && counter_value != 4'b0000) |=> counter_value == ($past(counter_value) - 4'd1)
    );

    // In down mode, 0 wraps to 15.
    check_down_wrap: assert property (
        @(posedge clk) disable iff (reset)
        (mode == 1'b1 && counter_value == 4'b0000) |=> counter_value == 4'b1111
    );

endmodule