module reg_shifter_sva(
    input logic        clk,
    input logic [31:0] rt_out,
    input logic [1:0]  mem_addr_in,
    input logic        MemWrite,
    input logic [5:0]  IR_out,
    input logic [31:0] rt_out_shift,
    input logic [3:0]  mem_byte_write_out
);

    // MemWrite low suppresses all byte write enables.
    check_memwrite_masks_all_bytes: assert property (
        @(posedge clk) !MemWrite |-> (mem_byte_write_out == 4'b0000)
    );

    // Store-word opcode passes rt_out through unchanged.
    check_sw_shift_passthrough: assert property (
        @(posedge clk) (IR_out == 6'b101011) |-> (rt_out_shift == rt_out)
    );

    // Store-word opcode enables all byte lanes when writing.
    check_sw_full_byte_enable: assert property (
        @(posedge clk) (IR_out == 6'b101011 && MemWrite) |-> (mem_byte_write_out == 4'b1111)
    );

    // Non-store-word at address 00 moves the low byte into the top byte lane.
    check_addr00_shift: assert property (
        @(posedge clk) (IR_out != 6'b101011 && mem_addr_in == 2'b00) |-> (rt_out_shift == {rt_out[7:0], 24'b0})
    );

    // Non-store-word at address 00 enables only the top byte lane when writing.
    check_addr00_byte_enable: assert property (
        @(posedge clk) (IR_out != 6'b101011 && mem_addr_in == 2'b00 && MemWrite) |-> (mem_byte_write_out == 4'b1000)
    );

    // Non-store-word at address 01 moves the low halfword into the top halfword lanes.
    check_addr01_shift: assert property (
        @(posedge clk) (IR_out != 6'b101011 && mem_addr_in == 2'b01) |-> (rt_out_shift == {rt_out[15:0], 16'b0})
    );

    // Non-store-word at address 01 enables the upper two byte lanes when writing.
    check_addr01_byte_enable: assert property (
        @(posedge clk) (IR_out != 6'b101011 && mem_addr_in == 2'b01 && MemWrite) |-> (mem_byte_write_out == 4'b1100)
    );

    // Non-store-word at address 10 moves the low 24 bits into the upper three byte lanes.
    check_addr10_shift: assert property (
        @(posedge clk) (IR_out != 6'b101011 && mem_addr_in == 2'b10) |-> (rt_out_shift == {rt_out[23:0], 8'b0})
    );

    // Non-store-word at address 10 enables the upper three byte lanes when writing.
    check_addr10_byte_enable: assert property (
        @(posedge clk) (IR_out != 6'b101011 && mem_addr_in == 2'b10 && MemWrite) |-> (mem_byte_write_out == 4'b1110)
    );

    // Non-store-word at address 11 passes rt_out through unchanged.
    check_addr11_shift_passthrough: assert property (
        @(posedge clk) (IR_out != 6'b101011 && mem_addr_in == 2'b11) |-> (rt_out_shift == rt_out)
    );

    // Non-store-word at address 11 enables all byte lanes when writing.
    check_addr11_full_byte_enable: assert property (
        @(posedge clk) (IR_out != 6'b101011 && mem_addr_in == 2'b11 && MemWrite) |-> (mem_byte_write_out == 4'b1111)
    );

endmodule