module onehot0_sva (
    input logic        clk,
    input logic [31:0] in,
    input logic        out
);

    // out must equal the implemented Boolean expression.
    check_out_matches_rtl_expression: assert property (
        @(posedge clk)
        out == (((in & (in - 32'd1)) == 32'd0) && (in[0] == 1'b0))
    );

    // Any input with bit 0 set forces out low.
    check_lsb_one_forces_out_low: assert property (
        @(posedge clk)
        in[0] |-> !out
    );

    // All-zero input produces a high output.
    check_zero_input_sets_out_high: assert property (
        @(posedge clk)
        (in == 32'd0) |-> out
    );

    // A nonzero one-hot input above bit 0 produces a high output.
    check_upper_onehot_sets_out_high: assert property (
        @(posedge clk)
        ((in != 32'd0) && ((in & (in - 32'd1)) == 32'd0) && (in[0] == 1'b0)) |-> out
    );

    // Inputs with multiple set bits produce a low output.
    check_multi_bit_input_clears_out: assert property (
        @(posedge clk)
        ((in & (in - 32'd1)) != 32'd0) |-> !out
    );

endmodule