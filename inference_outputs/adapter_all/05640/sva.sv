module if_stage_sva (
    input logic clk,
    input logic rst,
    input logic if_id_write_en,
    input logic pc_write,
    input logic [1:0] pc_source,
    input logic pstop_i,
    input logic i_read_en,
    input logic [31:0] i_addr,
    input logic [31:0] i_instr_in,
    input logic [31:0] jump_addr,
    input logic [31:0] branch_addr,
    input logic [31:0] reg_data_1,
    input logic [31:0] IF_ID_next_i_addr,
    input logic [31:0] IF_ID_instruction
);
    // i_read_en is permanently asserted HIGH.
    check_i_read_en_const: assert property (
        @(posedge clk) disable iff (rst) i_read_en == 1'b1
    );

    // i_addr is pc_reg >> 2.
    check_i_addr_mapping: assert property (
        @(posedge clk) disable iff (rst) i_addr == ($past(pc_reg) >> 2)
    );

    // pc_reg holds its value when pc_write is LOW.
    check_pc_hold_when_not_write: assert property (
        @(posedge clk) disable iff (rst) (!pc_write) |-> (pc_reg == $past(pc_reg))
    );

    // pc_reg loads pc_next when pc_write is HIGH and not stopped/memop.
    check_pc_load_when_write: assert property (
        @(posedge clk) disable iff (rst) (pc_write && !(pstop_i || ((i_instr_in[31:26] == 6'b100011) || (i_instr_in[31:26] == 6'b101011)))) |-> (pc_reg == $past(pc_next))
    );

    // pc_next selects next_i_addr for pc_source 00.
    check_pc_next_select_00: assert property (
        @(posedge clk) disable iff (rst) (pc_source == 2'b00) |-> (pc_next == ($past(pc_reg) + 4))
    );

    // pc_next selects branch_addr for pc_source 01.
    check_pc_next_select_01: assert property (
        @(posedge clk) disable iff (rst) (pc_source == 2'b01) |-> (pc_next == $past(branch_addr))
    );

    // pc_next selects jump_addr for pc_source 10.
    check_pc_next_select_10: assert property (
        @(posedge clk) disable iff (rst) (pc_source == 2'b10) |-> (pc_next == $past(jump_addr))
    );

    // pc_next selects reg_data_1 for pc_source 11.
    check_pc_next_select_11: assert property (
        @(posedge clk) disable iff (rst) (pc_source == 2'b11) |-> (pc_next == $past(reg_data_1))
    );

    // IF_ID_next_i_addr holds when if_id_write_en is LOW.
    check_if_id_next_i_addr_hold_when_not_write: assert property (
        @(posedge clk) disable iff (rst) (!if_id_write_en) |-> (IF_ID_next_i_addr == $past(IF_ID_next_i_addr))
    );

    // IF_ID_next_i_addr loads next_i_addr when if_id_write_en is HIGH.
    check_if_id_next_i_addr_load_when_write: assert property (
        @(posedge clk) disable iff (rst) if_id_write_en |-> (IF_ID_next_i_addr == ($past(pc_reg) + 4))
    );

    // IF_ID_instruction holds when if_id_write_en is LOW.
    check_if_id_instruction_hold_when_not_write: assert property (
        @(posedge clk) disable iff (rst) (!if_id_write_en) |-> (IF_ID_instruction == $past(IF_ID_instruction))
    );

    // IF_ID_instruction loads zero when if_id_write_en is HIGH and stopped/memop.
    check_if_id_instruction_zero_when_blocked: assert property (
        @(posedge clk) disable iff (rst) (if_id_write_en && (pstop_i || ((i_instr_in[31:26] == 6'b100011) || (i_instr_in[31:26] == 6'b101011)))) |-> (IF_ID_instruction == 32'h00000000)
    );

    // IF_ID_instruction loads i_instr_in when if_id_write_en is HIGH and not blocked.
    check_if_id_instruction_load_when_write: assert property (
        @(posedge clk) disable iff (rst) (if_id_write_en && !(pstop_i || ((i_instr_in[31:26] == 6'b100011) || (i_instr_in[31:26] == 6'b101011)))) |-> (IF_ID_instruction == $past(i_instr_in))
    );
endmodule