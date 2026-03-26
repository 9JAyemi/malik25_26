module top_module_sva (
    input logic        clk,
    input logic        reset,
    input logic        pause,
    input logic        up_down,
    input logic [15:0] q,
    input logic [15:0] up_count,
    input logic [15:0] down_count
);

    // Clock: clk; reset: active-high synchronous; counters are sequential and q is combinational.
    
    // The up counter loads zero on reset.
    check_up_count_reset: assert property (
        @(posedge clk) reset |=> (up_count == 16'h0000)
    );

    // The down counter loads all ones on reset.
    check_down_count_reset: assert property (
        @(posedge clk) reset |=> (down_count == 16'hFFFF)
    );

    // The up counter increments by one when not paused.
    check_up_count_increment: assert property (
        @(posedge clk) disable iff (reset)
        (!$initstate && !pause) |=> (up_count == ($past(up_count) + 16'd1))
    );

    // The up counter holds its value when paused.
    check_up_count_hold_on_pause: assert property (
        @(posedge clk) disable iff (reset)
        (!$initstate && pause) |=> (up_count == $past(up_count))
    );

    // The down counter decrements by one when not paused.
    check_down_count_decrement: assert property (
        @(posedge clk) disable iff (reset)
        (!$initstate && !pause) |=> (down_count == ($past(down_count) - 16'd1))
    );

    // The down counter holds its value when paused.
    check_down_count_hold_on_pause: assert property (
        @(posedge clk) disable iff (reset)
        (!$initstate && pause) |=> (down_count == $past(down_count))
    );

    // The output mux selects the requested counter.
    check_q_mux_behavior: assert property (
        @(posedge clk) disable iff (reset)
        (q == (up_down ? down_count : up_count))
    );

    // After reset, q reflects the selected reset value.
    check_q_reset_value: assert property (
        @(posedge clk) reset |=> (q == (up_down ? 16'hFFFF : 16'h0000))
    );

endmodule