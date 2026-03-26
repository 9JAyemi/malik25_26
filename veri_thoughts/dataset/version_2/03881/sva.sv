module decoder_sva (
    input logic        clk,
    input logic [4:0]  encode_in,
    input logic [31:0] data_out
);

    // data_out is always zero or one-hot.
    check_data_out_onehot0: assert property (
        @(posedge clk) disable iff (1'b0)
        $onehot0(data_out)
    );

    // Only bits 1, 2, 4, 8, and 16 can ever be set.
    check_data_out_valid_bit_positions: assert property (
        @(posedge clk) disable iff (1'b0)
        ((data_out & ~32'h00010116) == 32'h00000000)
    );

    // Bit 0 is never driven high by this RTL.
    check_data_out_bit0_low: assert property (
        @(posedge clk) disable iff (1'b0)
        (data_out[0] == 1'b0)
    );

    // encode_in == 0 selects bit 1.
    check_encode_0_pattern: assert property (
        @(posedge clk) disable iff (1'b0)
        (encode_in == 5'd0) |-> (data_out == 32'h00000002)
    );

    // encode_in == 1 selects bit 2.
    check_encode_1_pattern: assert property (
        @(posedge clk) disable iff (1'b0)
        (encode_in == 5'd1) |-> (data_out == 32'h00000004)
    );

    // encode_in == 2 selects bit 4.
    check_encode_2_pattern: assert property (
        @(posedge clk) disable iff (1'b0)
        (encode_in == 5'd2) |-> (data_out == 32'h00000010)
    );

    // encode_in == 3 selects bit 8.
    check_encode_3_pattern: assert property (
        @(posedge clk) disable iff (1'b0)
        (encode_in == 5'd3) |-> (data_out == 32'h00000100)
    );

    // encode_in == 4 selects bit 16.
    check_encode_4_pattern: assert property (
        @(posedge clk) disable iff (1'b0)
        (encode_in == 5'd4) |-> (data_out == 32'h00010000)
    );

    // encode_in values 5 through 31 leave data_out at zero.
    check_encode_ge5_zero: assert property (
        @(posedge clk) disable iff (1'b0)
        (encode_in >= 5'd5) |-> (data_out == 32'h00000000)
    );

endmodule