module top_module_sva (
    input logic clk,
    input logic reset,
    input logic [99:0] in,
    input logic [7:0] a, b, c, d,
    input logic [7:0] min,
    input logic out,
    input logic [1:0] priority_out,
    input logic [7:0] mux_out,
    input logic out_and,
    input logic out_or,
    input logic out_xor
);

    // priority_out selects 00 when a is greater than b, c, and d.
    check_priority_select_a: assert property (
        @(posedge clk) disable iff (reset)
        (a > b && a > c && a > d) |-> (priority_out == 2'b00)
    );

    // priority_out selects 01 when b is greater than c and d.
    check_priority_select_b: assert property (
        @(posedge clk) disable iff (reset)
        ((a <= b) && (b > c) && (b > d)) |-> (priority_out == 2'b01)
    );

    // priority_out selects 10 when c is greater than d.
    check_priority_select_c: assert property (
        @(posedge clk) disable iff (reset)
        ((a <= b) && (b <= c) && (c > d)) |-> (priority_out == 2'b10)
    );

    // priority_out selects 11 when d is the largest input.
    check_priority_select_d: assert property (
        @(posedge clk) disable iff (reset)
        ((a <= b) && (b <= c) && (c <= d)) |-> (priority_out == 2'b11)
    );

    // mux_out matches a when priority_out selects 00.
    check_mux_select_a: assert property (
        @(posedge clk) disable iff (reset)
        (priority_out == 2'b00) |-> (mux_out == a)
    );

    // mux_out matches b when priority_out selects 01.
    check_mux_select_b: assert property (
        @(posedge clk) disable iff (reset)
        (priority_out == 2'b01) |-> (mux_out == b)
    );

    // mux_out matches c when priority_out selects 10.
    check_mux_select_c: assert property (
        @(posedge clk) disable iff (reset)
        (priority_out == 2'b10) |-> (mux_out == c)
    );

    // mux_out matches d when priority_out selects 11.
    check_mux_select_d: assert property (
        @(posedge clk) disable iff (reset)
        (priority_out == 2'b11) |-> (mux_out == d)
    );

    // min is the output of the mux stage.
    check_min_matches_mux_out: assert property (
        @(posedge clk) disable iff (reset)
        (min == mux_out)
    );

    // out_and is the AND reduction of the first 50 input bits.
    check_out_and_definition: assert property (
        @(posedge clk) disable iff (reset)
        (out_and == (&in[49:0]))
    );

    // out_or is the OR reduction of the first 50 input bits.
    check_out_or_definition: assert property (
        @(posedge clk) disable iff (reset)
        (out_or == (|in[49:0]))
    );

    // out_xor is the XOR reduction of the first 50 input bits.
    check_out_xor_definition: assert property (
        @(posedge clk) disable iff (reset)
        (out_xor == (^in[49:0]))
    );

    // out is the OR of out_and, out_or, and out_xor.
    check_out_definition: assert property (
        @(posedge clk) disable iff (reset)
        (out == (out_and | out_or | out_xor))
    );

endmodule