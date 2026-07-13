module padder_sva (
    input logic        clk,
    input logic [31:0] in,
    input logic [1:0]  byte_num,
    input logic [31:0] out
);

    // External clock is used only to sample this combinational DUT.

    // byte_num 0 selects the fixed padding value.
    check_byte0_constant_padding: assert property (
        @(posedge clk) (byte_num == 2'd0) |-> (out == 32'h01000000)
    );

    // byte_num 1 preserves the upper 24 bits and sets the low byte to 01.
    check_byte1_low_byte_padding: assert property (
        @(posedge clk) (byte_num == 2'd1) |-> (out == {in[31:8], 8'h01})
    );

    // byte_num 2 preserves the upper 16 bits and sets the low halfword to 0100.
    check_byte2_low_halfword_padding: assert property (
        @(posedge clk) (byte_num == 2'd2) |-> (out == {in[31:16], 16'h0100})
    );

    // byte_num 3 preserves the upper 8 bits and sets the low 24 bits to 010000.
    check_byte3_low_24bit_padding: assert property (
        @(posedge clk) (byte_num == 2'd3) |-> (out == {in[31:24], 24'h010000})
    );

endmodule