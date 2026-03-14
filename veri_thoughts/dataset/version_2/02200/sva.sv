module Control_sva (
    input logic [5:0] opcode,
    input logic clk,
    input logic reg_dst,
    input logic jump,
    input logic branch,
    input logic ctrl_mem_read,
    input logic mem_to_reg,
    input logic ctrl_mem_write,
    input logic alu_src,
    input logic reg_write,
    input logic [1:0] alu_op
);

    // R-type decode from previous opcode cycle.
    decode_rtype: assert property (
        @(posedge clk)
            ($past(opcode) == 6'b000000)
            |-> (reg_dst == 1'b1 && alu_src == 1'b0 && mem_to_reg == 1'b0 && reg_write == 1'b1 &&
                 ctrl_mem_read == 1'b0 && ctrl_mem_write == 1'b0 && branch == 1'b0 && jump == 1'b0 && alu_op == 2'b10)
    );

    // LW decode from previous opcode cycle.
    decode_lw: assert property (
        @(posedge clk)
            ($past(opcode) == 6'b100011)
            |-> (reg_dst == 1'b0 && alu_src == 1'b1 && mem_to_reg == 1'b1 && reg_write == 1'b1 &&
                 ctrl_mem_read == 1'b1 && ctrl_mem_write == 1'b0 && branch == 1'b0 && jump == 1'b0 && alu_op == 2'b00)
    );

    // SW decode from previous opcode cycle.
    decode_sw: assert property (
        @(posedge clk)
            ($past(opcode) == 6'b101011)
            |-> (reg_dst == 1'b0 && alu_src == 1'b1 && mem_to_reg == 1'b0 && reg_write == 1'b0 &&
                 ctrl_mem_read == 1'b0 && ctrl_mem_write == 1'b1 && branch == 1'b0 && jump == 1'b0 && alu_op == 2'b00)
    );

    // BEQ decode from previous opcode cycle.
    decode_beq: assert property (
        @(posedge clk)
            ($past(opcode) == 6'b000100)
            |-> (reg_dst == 1'b0 && alu_src == 1'b0 && mem_to_reg == 1'b0 && reg_write == 1'b0 &&
                 ctrl_mem_read == 1'b0 && ctrl_mem_write == 1'b0 && branch == 1'b1 && jump == 1'b0 && alu_op == 2'b01)
    );

    // ADDI decode from previous opcode cycle.
    decode_addi: assert property (
        @(posedge clk)
            ($past(opcode) == 6'b001000)
            |-> (reg_dst == 1'b0 && alu_src == 1'b1 && mem_to_reg == 1'b0 && reg_write == 1'b1 &&
                 ctrl_mem_read == 1'b0 && ctrl_mem_write == 1'b0 && branch == 1'b0 && jump == 1'b0 && alu_op == 2'b00)
    );

    // JUMP decode from previous opcode cycle.
    decode_jump: assert property (
        @(posedge clk)
            ($past(opcode) == 6'b000010)
            |-> (reg_dst == 1'b0 && alu_src == 1'b0 && mem_to_reg == 1'b0 && reg_write == 1'b0 &&
                 ctrl_mem_read == 1'b0 && ctrl_mem_write == 1'b0 && branch == 1'b0 && jump == 1'b1 && alu_op == 2'b00)
    );

    // Unrecognized opcode in previous cycle drives all controls low and ALUop=00.
    decode_default_other: assert property (
        @(posedge clk)
            ($past(opcode) != 6'b000000) && ($past(opcode) != 6'b100011) && ($past(opcode) != 6'b101011) &&
            ($past(opcode) != 6'b000100) && ($past(opcode) != 6'b001000) && ($past(opcode) != 6'b000010)
            |-> (reg_dst == 1'b0 && alu_src == 1'b0 && mem_to_reg == 1'b0 && reg_write == 1'b0 &&
                 ctrl_mem_read == 1'b0 && ctrl_mem_write == 1'b0 && branch == 1'b0 && jump == 1'b0 && alu_op == 2'b00)
    );

    // Read and write to memory are never asserted together.
    check_mem_rw_mutex: assert property (
        @(posedge clk) (!$isunknown({ctrl_mem_read, ctrl_mem_write})) |-> !(ctrl_mem_read && ctrl_mem_write)
    );

    // mem_to_reg matches mem_read behavior (both high only for LW).
    check_mem_to_reg_eq_mem_read: assert property (
        @(posedge clk) (!$isunknown({mem_to_reg, ctrl_mem_read})) |-> (mem_to_reg == ctrl_mem_read)
    );

    // ALU operation is only 00, 01, or 10 (never 11).
    check_alu_op_range: assert property (
        @(posedge clk) (!$isunknown(alu_op)) |-> (alu_op != 2'b11)
    );

endmodule