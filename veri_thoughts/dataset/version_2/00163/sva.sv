module decoder_4to16_assertions (
    input logic        clk,
    input logic [3:0]  input_bits,
    input logic [15:0] output_bits
);

    // Input 0 decodes to bit 0.
    check_decode_0: assert property (
        @(posedge clk) (input_bits == 4'b0000) |-> (output_bits == 16'b0000000000000001)
    );

    // Input 1 decodes to bit 1.
    check_decode_1: assert property (
        @(posedge clk) (input_bits == 4'b0001) |-> (output_bits == 16'b0000000000000010)
    );

    // Input 2 decodes to bit 2.
    check_decode_2: assert property (
        @(posedge clk) (input_bits == 4'b0010) |-> (output_bits == 16'b0000000000000100)
    );

    // Input 3 decodes to bit 3.
    check_decode_3: assert property (
        @(posedge clk) (input_bits == 4'b0011) |-> (output_bits == 16'b0000000000001000)
    );

    // Input 4 decodes to bit 4.
    check_decode_4: assert property (
        @(posedge clk) (input_bits == 4'b0100) |-> (output_bits == 16'b0000000000010000)
    );

    // Input 5 decodes to bit 5.
    check_decode_5: assert property (
        @(posedge clk) (input_bits == 4'b0101) |-> (output_bits == 16'b0000000000100000)
    );

    // Input 6 decodes to bit 6.
    check_decode_6: assert property (
        @(posedge clk) (input_bits == 4'b0110) |-> (output_bits == 16'b0000000001000000)
    );

    // Input 7 decodes to bit 7.
    check_decode_7: assert property (
        @(posedge clk) (input_bits == 4'b0111) |-> (output_bits == 16'b0000000010000000)
    );

    // Input 8 decodes to bit 8.
    check_decode_8: assert property (
        @(posedge clk) (input_bits == 4'b1000) |-> (output_bits == 16'b0000000100000000)
    );

    // Input 9 decodes to bit 9.
    check_decode_9: assert property (
        @(posedge clk) (input_bits == 4'b1001) |-> (output_bits == 16'b0000001000000000)
    );

    // Input 10 decodes to bit 10.
    check_decode_10: assert property (
        @(posedge clk) (input_bits == 4'b1010) |-> (output_bits == 16'b0000010000000000)
    );

    // Input 11 decodes to bit 11.
    check_decode_11: assert property (
        @(posedge clk) (input_bits == 4'b1011) |-> (output_bits == 16'b0000100000000000)
    );

    // Input 12 decodes to bit 12.
    check_decode_12: assert property (
        @(posedge clk) (input_bits == 4'b1100) |-> (output_bits == 16'b0001000000000000)
    );

    // Input 13 decodes to bit 13.
    check_decode_13: assert property (
        @(posedge clk) (input_bits == 4'b1101) |-> (output_bits == 16'b0010000000000000)
    );

    // Input 14 decodes to bit 14.
    check_decode_14: assert property (
        @(posedge clk) (input_bits == 4'b1110) |-> (output_bits == 16'b0100000000000000)
    );

    // Input 15 decodes to bit 15.
    check_decode_15: assert property (
        @(posedge clk) (input_bits == 4'b1111) |-> (output_bits == 16'b1000000000000000)
    );

endmodule