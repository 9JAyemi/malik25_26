module mux_add_sub_sva (
    input logic clk,
    input logic [7:0] a,
    input logic [7:0] b,
    input logic select_ctrl,
    input logic add_sub_ctrl,
    input logic [3:0] Q
);

// Q is zero when the multiplexer is disabled.
    check_mux_disabled_zero: assert property (
        @(posedge clk) !add_sub_ctrl |-> (Q == 4'h0)
    );

// Q matches the lower nibble of the add result when enabled.
    check_add_result_lower_nibble: assert property (
        @(posedge clk) add_sub_ctrl |-> (Q == (a + b)[3:0])
    );

// Q is zero when the add result has zero in the lower nibble.
    check_add_zero_lower_nibble: assert property (
        @(posedge clk) add_sub_ctrl && ((a + b) == 8'h00) |-> (Q == 4'h0)
    );

// Q matches the lower nibble of the subtract result when enabled.
    check_sub_result_lower_nibble: assert property (
        @(posedge clk) !add_sub_ctrl |-> (Q == (a - b)[3:0])
    );

// Q is zero when the subtract result has zero in the lower nibble.
    check_sub_zero_lower_nibble: assert property (
        @(posedge clk) !add_sub_ctrl && ((a - b) == 8'h00) |-> (Q == 4'h0)
    );

endmodule
