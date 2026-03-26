module top_module_assertions (
    input logic        a,
    input logic        b,
    input logic        c,
    input logic [15:0] in,
    input logic [7:0]  out_hi,
    input logic [7:0]  out_lo,
    input logic [23:0] final_out
);

    // Purely combinational DUT; assertions sample on the formal global clock.

    // out_hi must mirror the upper byte of in.
    check_out_hi_split: assert property (
        @($global_clock)
        out_hi == in[15:8]
    );

    // out_lo must mirror the lower byte of in.
    check_out_lo_split: assert property (
        @($global_clock)
        out_lo == in[7:0]
    );

    // final_out must equal the sum of a, b, b, c, and the two input bytes.
    check_final_out_function: assert property (
        @($global_clock)
        final_out == ({23'b0, a} +
                      {23'b0, b} +
                      {23'b0, b} +
                      {23'b0, c} +
                      {16'b0, in[15:8]} +
                      {16'b0, in[7:0]})
    );

    // The upper byte of final_out must remain zero.
    check_final_out_upper_byte_zero: assert property (
        @($global_clock)
        final_out[23:16] == 8'h00
    );

    // With no control-bit contribution, final_out must be the sum of the split bytes.
    check_data_only_sum: assert property (
        @($global_clock)
        (!a && !b && !c) |-> (final_out == ({16'b0, out_hi} + {16'b0, out_lo}))
    );

    // With zero input data, final_out must be the sum of the control-bit paths.
    check_control_only_sum: assert property (
        @($global_clock)
        (in == 16'h0000) |-> (final_out == ({23'b0, a} +
                                            {23'b0, b} +
                                            {23'b0, b} +
                                            {23'b0, c}))
    );

    // All-zero inputs must produce all-zero outputs.
    check_zero_inputs_zero_outputs: assert property (
        @($global_clock)
        (!a && !b && !c && (in == 16'h0000)) |->
            ((out_hi == 8'h00) && (out_lo == 8'h00) && (final_out == 24'h000000))
    );

    // If only b is high and in is zero, b must contribute twice.
    check_b_double_contribution: assert property (
        @($global_clock)
        (!a && b && !c && (in == 16'h0000)) |-> (final_out == 24'd2)
    );

endmodule