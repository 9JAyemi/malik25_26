module split_16bit_input_sva (
    input logic        clk,
    input logic [15:0] in,
    input logic [7:0]  out_hi,
    input logic [7:0]  out_lo
);

    // out_lo selects the low or high input byte based on in[8].
    check_out_lo_selected_byte: assert property (
        @(posedge clk) out_lo == (in[8] ? in[15:8] : in[7:0])
    );

    // out_hi selects the complementary input byte based on in[8].
    check_out_hi_selected_byte: assert property (
        @(posedge clk) out_hi == (in[8] ? in[7:0] : in[15:8])
    );

    // When in[8] is low, the outputs preserve the original byte order.
    check_original_order_when_sel_low: assert property (
        @(posedge clk) !in[8] |-> ({out_hi, out_lo} == {in[15:8], in[7:0]})
    );

    // When in[8] is high, the outputs swap the input byte order.
    check_swapped_order_when_sel_high: assert property (
        @(posedge clk) in[8] |-> ({out_hi, out_lo} == {in[7:0], in[15:8]})
    );

    // The outputs are always the two input bytes in one of the two possible orders.
    check_outputs_form_input_byte_permutation: assert property (
        @(posedge clk) (({out_hi, out_lo} == {in[15:8], in[7:0]}) ||
                        ({out_hi, out_lo} == {in[7:0], in[15:8]}))
    );

    // The two outputs are equal exactly when the two input bytes are equal.
    check_output_equality_matches_input_equality: assert property (
        @(posedge clk) ((out_hi == out_lo) == (in[15:8] == in[7:0]))
    );

endmodule