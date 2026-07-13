module top_module_sva (
    input logic clk,
    input logic reset,
    input logic [99:0] in,
    input logic [7:0] a, b, c, d,
    input logic [7:0] min,
    input logic out
);

    // No RTL clock or reset; sample combinational behavior on clk.

    // min must match the selected input value.
    check_min_matches_selected_input: assert property (
        @(posedge clk) disable iff (reset)
        (min == ((a > b && a > c && a > d) ? a :
                 ((b > c && b > d) ? b :
                  ((c > d) ? c : d))))
    );

    // out must be the OR of the three comb_logic outputs.
    check_out_matches_comb_logic_or: assert property (
        @(posedge clk) disable iff (reset)
        (out == ((&in[49:0]) | (|in[49:0]) | (^in[49:0])))
    );

    // out must equal the reduction XOR of the lower 50 input bits.
    check_out_matches_lower_half_xor: assert property (
        @(posedge clk) disable iff (reset)
        (out == (^in[49:0]))
    );

    // out must equal the reduction XOR of the upper 50 input bits.
    check_out_matches_upper_half_xor: assert property (
        @(posedge clk) disable iff (reset)
        (out == (^in[99:50]))
    );

    // out must equal the reduction XOR of the entire input bus.
    check_out_matches_full_input_xor: assert property (
        @(posedge clk) disable iff (reset)
        (out == (^in))
    );

    // If the lower half is all zeros, out must be the XOR of the upper half.
    check_out_lower_zero_upper_xor: assert property (
        @(posedge clk) disable iff (reset)
        ((&in[49:0]) == 1'b0) |-> (out == (^in[99:50]))
    );

    // If the upper half is all zeros, out must be the XOR of the lower half.
    check_out_upper_zero_lower_xor: assert property (
        @(posedge clk) disable iff (reset)
        ((&in[99:50]) == 1'b0) |-> (out == (^in[49:0]))
    );

    // If the entire input bus is all zeros, out must be zero.
    check_out_zero_when_input_zero: assert property (
        @(posedge clk) disable iff (reset)
        ((&in) == 1'b0) |-> (out == 1'b0)
    );

    // If the entire input bus is all ones, out must be zero.
    check_out_zero_when_input_all_ones: assert property (
        @(posedge clk) disable iff (reset)
        ((|in) == 1'b1) |-> (out == 1'b0)
    );

    // If the input bus is exactly half ones and half zeros, out must be one.
    check_out_one_when_input_equal_ones_zeros: assert property (
        @(posedge clk) disable iff (reset)
        (((&in) == 1'b1) && ((|in) == 1'b1)) |-> (out == 1'b1)
    );

endmodule