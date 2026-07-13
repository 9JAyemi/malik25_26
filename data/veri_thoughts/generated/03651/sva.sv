module decoder_3to8_sva (
    input logic        clk,
    input logic [2:0]  in,
    input logic [7:0]  out
);

    // Output matches the decoder equation.
    check_decode_equation: assert property (
        @(posedge clk) out == (8'b00000001 << in)
    );

    // Decoder output is always one-hot.
    check_out_is_onehot: assert property (
        @(posedge clk) $onehot(out)
    );

    // Input 0 selects output bit 0.
    check_in_0_decodes_bit0: assert property (
        @(posedge clk) (in == 3'd0) |-> (out == 8'b00000001)
    );

    // Input 1 selects output bit 1.
    check_in_1_decodes_bit1: assert property (
        @(posedge clk) (in == 3'd1) |-> (out == 8'b00000010)
    );

    // Input 2 selects output bit 2.
    check_in_2_decodes_bit2: assert property (
        @(posedge clk) (in == 3'd2) |-> (out == 8'b00000100)
    );

    // Input 3 selects output bit 3.
    check_in_3_decodes_bit3: assert property (
        @(posedge clk) (in == 3'd3) |-> (out == 8'b00001000)
    );

    // Input 4 selects output bit 4.
    check_in_4_decodes_bit4: assert property (
        @(posedge clk) (in == 3'd4) |-> (out == 8'b00010000)
    );

    // Input 5 selects output bit 5.
    check_in_5_decodes_bit5: assert property (
        @(posedge clk) (in == 3'd5) |-> (out == 8'b00100000)
    );

    // Input 6 selects output bit 6.
    check_in_6_decodes_bit6: assert property (
        @(posedge clk) (in == 3'd6) |-> (out == 8'b01000000)
    );

    // Input 7 selects output bit 7.
    check_in_7_decodes_bit7: assert property (
        @(posedge clk) (in == 3'd7) |-> (out == 8'b10000000)
    );

endmodule