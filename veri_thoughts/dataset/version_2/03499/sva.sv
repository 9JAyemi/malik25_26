module padder1_sva (
    input logic        clk,
    input logic [31:0] in,
    input logic [1:0]  byte_num,
    input logic [31:0] out
);

    // byte_num 0 drives the fixed 0x01000000 padding value.
    check_byte0_constant: assert property (
        @(posedge clk) (byte_num == 2'd0) |-> (out == 32'h01000000)
    );

    // byte_num 1 preserves the top byte and pads the lower 24 bits.
    check_byte1_mapping: assert property (
        @(posedge clk) (byte_num == 2'd1) |-> (out == {in[31:24], 24'h010000})
    );

    // byte_num 2 preserves the top two bytes and pads the lower 16 bits.
    check_byte2_mapping: assert property (
        @(posedge clk) (byte_num == 2'd2) |-> (out == {in[31:16], 16'h0100})
    );

    // byte_num 3 preserves the top three bytes and pads the low byte.
    check_byte3_mapping: assert property (
        @(posedge clk) (byte_num == 2'd3) |-> (out == {in[31:8], 8'h01})
    );

endmodule