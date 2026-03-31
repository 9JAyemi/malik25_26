```systemverilog
module if_stage_sva (
    input logic clk,
    input logic rst,
    input logic if_id_write_en,
    input logic pc_write,
    input logic [1:0] pc_source,
    input logic pstop_i,
    input logic [31:0] i_instr_in, jump_addr, branch_addr, reg_data_1,
    output logic i_read_en,
    output logic [31:0] i_addr,
    input logic [31:0] IF_ID_next_i_addr,
    input logic [31:0] IF_ID_instruction
);
    // Sequential logic for PC register
    pc_update: assert property (
        @(posedge clk) disable iff (!rst) pc_reg == pc_next
    ) else $error("PC register update mismatch");

    // Sequential logic for IF_ID_next_i_addr and IF_ID_instruction
    if_id_update: assert property (
        @(posedge clk) disable iff (!rst) IF_ID_next_i_addr == next_i_addr && IF_ID_instruction == i_instr_in
    ) else $error("IF_ID register update mismatch");

    // Combinational logic for i_read_en and i_addr
    i_read_en_check: assert property (
        @(posedge clk) disable iff (!rst) i_read_en == 1'b1
    ) else $error("i_read_en should always be 1");

    i_addr_check: assert property (
        @(posedge clk) disable iff (!rst) i_addr == pc_reg >> 2
    ) else $error("i_addr should be PC register shifted right by 2");

    // PC source logic
    pc_source_00: assert property (
        @(posedge clk) disable iff (!rst) (pc_source == 2'b00) |-> pc_next == pc_reg + 4
    ) else $error("PC source 00 should update PC to next instruction address");

    pc_source_01: assert property (
        @(posedge clk) disable iff (!rst) (pc_source == 2'b01) |-> pc_next == branch_addr
    ) else $error("PC source 01 should update PC to branch address");

    pc_source_10: assert property (
        @(posedge clk) disable iff (!rst) (pc_source == 2'b10) |-> pc_next == jump_addr
    ) else $error("PC source 10 should update PC to jump address");

    pc_source_11: assert property (
        @(posedge clk) disable iff (!rst) (pc_source == 2'b11) |-> pc_next == reg_data_1
    ) else $error("PC source 11 should update PC to register data 1");

    // Reset behavior
    reset_behavior: assert property (
        @(posedge clk) !rst |-> (pc_reg == 0 && IF_ID_next_i_addr == 0 && IF_ID_instruction == 0)
    ) else $error("Reset should drive all registers to 0");

endmodule
```