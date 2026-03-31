module top_module_sva (
    input logic clk,
    input logic reset,
    input logic [31:0] in,
    input logic [31:0] out
);

// Reset clears the output on the next clock.
    check_reset_clears_out: assert property (
        @(posedge clk) reset |=> (out == 32'h0000_0000)
    );

// A rising edge on the input is detected on the next clock.
    check_rising_edge_detected: assert property (
        @(posedge clk) disable iff (reset)
        $rose(in) |=> (out == in)
    );

// A falling edge on the input is not detected on the next clock.
    check_falling_edge_not_detected: assert property (
        @(posedge clk) disable iff (reset)
        $fell(in) |=> (out == 32'h0000_0000)
    );

// A stable input value is not detected on the next clock.
    check_stable_input_not_detected: assert property (
        @(posedge clk) disable iff (reset)
        $stable(in) |=> (out == 32'h0000_0000)
    );

// The output matches the input from the previous clock.
    check_out_matches_previous_input: assert property (
        @(posedge clk) disable iff (reset)
        1'b1 |=> (out == $past(in))
    );

endmodule
