module top_module_sva (
    input logic clk,
    input logic reset,
    input logic [99:0] in,
    input logic [7:0] a, b, c, d,
    input logic [7:0] min,
    input logic out
);

// min must match the mux output selected by priority_encoder.
    check_min_matches_mux: assert property (
        @(posedge clk) disable iff (reset)
        min == (a > b && a > c && a > d ? a :
                b > c && b > d ? b :
                c > d ? c : d)
    );

// out must be the OR of the three comb_logic outputs.
    check_out_is_or_of_comb_outputs: assert property (
        @(posedge clk) disable iff (reset)
        out == (out_and | out_or | out_xor)
    );

// out_and must be the reduction AND of the lower 50 input bits.
    check_out_and_definition: assert property (
        @(posedge clk) disable iff (reset)
        out_and == (&in[49:0])
    );

// out_or must be the reduction OR of the lower 50 input bits.
    check_out_or_definition: assert property (
        @(posedge clk) disable iff (reset)
        out_or == (|in[49:0])
    );

// out_xor must be the reduction XOR of the lower 50 input bits.
    check_out_xor_definition: assert property (
        @(posedge clk) disable iff (reset)
        out_xor == (^in[49:0])
    );

// If all lower 50 input bits are zero, out must be zero.
    check_out_zero_when_all_zero: assert property (
        @(posedge clk) disable iff (reset)
        (&in[49:0]) |-> (out == 1'b0)
    );

// If any lower 50 input bit is one, out must be one.
    check_out_one_when_any_one: assert property (
        @(posedge clk) disable iff (reset)
        (|in[49:0]) |-> (out == 1'b1)
    );

// If all lower 50 input bits are one, out must be one.
    check_out_one_when_all_one: assert property (
        @(posedge clk) disable iff (reset)
        (|in[49:0] && &in[49:0]) |-> (out == 1'b1)
    );

// If all lower 50 input bits are zero, out_and must be zero.
    check_out_and_zero_when_all_zero: assert property (
        @(posedge clk) disable iff (reset)
        (&in[49:0]) |-> (out_and == 1'b0)
    );

// If any lower 50 input bit is one, out_and must be one.
    check_out_and_one_when_any_one: assert property (
        @(posedge clk) disable iff (reset)
        (|in[49:0]) |-> (out_and == 1'b1)
    );

// If all lower 50 input bits are one, out_and must be one.
    check_out_and_one_when_all_one: assert property (
        @(posedge clk) disable iff (reset)
        (|in[49:0] && &in[49:0]) |-> (out_and == 1'b1)
    );

// If all lower 50 input bits are zero, out_or must be zero.
    check_out_or_zero_when_all_zero: assert property (
        @(posedge clk) disable iff (reset)
        (&in[49:0]) |-> (out_or == 1'b0)
    );

// If any lower 50 input bit is one, out_or must be one.
    check_out_or_one_when_any_one: assert property (
        @(posedge clk) disable iff (reset)
        (|in[49:0]) |-> (out_or == 1'b1)
    );

// If all lower 50 input bits are one, out_or must be one.
    check_out_or_one_when_all_one: assert property (
        @(posedge clk) disable iff (reset)
        (|in[49:0] && &in[49:0]) |-> (out_or == 1'b1)
    );

// If all lower 50 input bits are zero, out_xor must be zero.
    check_out_xor_zero_when_all_zero: assert property (
        @(posedge clk) disable iff (reset)
        (&in[49:0]) |-> (out_xor == 1'b0)
    );

// If exactly one lower 50 input bit is one, out_xor must be one.
    check_out_xor_one_when_one_hot: assert property (
        @(posedge clk) disable iff (reset)
        ((|in[49:0]) && (&(~in[49:0]))) |-> (out_xor == 1'b1)
    );

// If more than one lower 50 input bit is one, out_xor must be zero.
    check_out_xor_zero_when_more_than_one: assert property (
        @(posedge clk) disable iff (reset)
        ((|in[49:0]) && ~(&in[49:0])) |-> (out_xor == 1'b0)
    );

// If all lower 50 input bits are one, out_xor must be zero.
    check_out_xor_zero_when_all_one: assert property (
        @(posedge clk) disable iff (reset)
        (|in[49:0] && &in[49:0]) |-> (out_xor == 1'b0)
    );

endmodule
