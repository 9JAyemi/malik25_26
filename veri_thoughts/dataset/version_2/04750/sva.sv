module mem_shifter_sva (
    input logic        clk,
    input logic [31:0] mem_data_out,
    input logic [1:0]  mem_addr_in,
    input logic [5:0]  IR_out,
    input logic [31:0] mem_data_shift,
    input logic [3:0]  Rd_write_byte_en
);

    localparam [5:0] LW_OPCODE = 6'b100011;

    // Word opcode passes all 32 bits and enables all bytes.
    check_word_opcode_passthrough: assert property (
        @(posedge clk)
        (IR_out == LW_OPCODE) |-> ((mem_data_shift == mem_data_out) &&
                                   (Rd_write_byte_en == 4'b1111))
    );

    // Non-word offset 0 passes all 32 bits and enables all bytes.
    check_nonword_addr_00: assert property (
        @(posedge clk)
        (IR_out != LW_OPCODE && mem_addr_in == 2'b00) |-> ((mem_data_shift == mem_data_out) &&
                                                           (Rd_write_byte_en == 4'b1111))
    );

    // Non-word offset 1 clears the low byte and disables byte 0.
    check_nonword_addr_01: assert property (
        @(posedge clk)
        (IR_out != LW_OPCODE && mem_addr_in == 2'b01) |-> ((mem_data_shift == {mem_data_out[31:8], 8'b0}) &&
                                                           (Rd_write_byte_en == 4'b1110))
    );

    // Non-word offset 2 clears the low two bytes and disables bytes 1:0.
    check_nonword_addr_10: assert property (
        @(posedge clk)
        (IR_out != LW_OPCODE && mem_addr_in == 2'b10) |-> ((mem_data_shift == {mem_data_out[31:16], 16'b0}) &&
                                                           (Rd_write_byte_en == 4'b1100))
    );

    // Non-word offset 3 clears the low three bytes and enables only byte 3.
    check_nonword_addr_11: assert property (
        @(posedge clk)
        (IR_out != LW_OPCODE && mem_addr_in == 2'b11) |-> ((mem_data_shift == {mem_data_out[31:24], 24'b0}) &&
                                                           (Rd_write_byte_en == 4'b1000))
    );

endmodule