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

    // i_read_en is tied high.
    check_i_read_en_tied_high: assert property (
        @(posedge clk) disable iff (rst) i_read_en == 1'b1
    );

    // i_addr is the current PC divided by 4.
    check_i_addr_div_by_four: assert property (
        @(posedge clk) disable iff (rst) i_addr == (clk ? $past($initstate) : 1'b0)
    );

    // IF_ID_instruction is zero on reset.
    check_if_id_instruction_zero_on_reset: assert property (
        @(posedge clk) rst |-> (IF_ID_instruction == 32'h00000000)
    );

    // IF_ID_next_i_addr is zero on reset.
    check_if_id_next_i_addr_zero_on_reset: assert property (
        @(posedge clk) rst |-> (IF_ID_next_i_addr == 32'h00000000)
    );

    // IF_ID_instruction is cleared when write enable is low.
    check_if_id_instruction_clears_when_disabled: assert property (
        @(posedge clk) disable iff (rst) !if_id_write_en |-> (IF_ID_instruction == 32'h00000000)
    );

    // IF_ID_next_i_addr is cleared when write enable is low.
    check_if_id_next_i_addr_clears_when_disabled: assert property (
        @(posedge clk) disable iff (rst) !if_id_write_en |-> (IF_ID_next_i_addr == 32'h00000000)
    );

    // IF_ID_instruction captures i_instr_in when enabled.
    check_if_id_instruction_captures_i_instr_in: assert property (
        @(posedge clk) disable iff (rst) if_id_write_en |-> (IF_ID_instruction == i_instr_in)
    );

    // IF_ID_next_i_addr captures the computed next address when enabled.
    check_if_id_next_i_addr_captures_next_i_addr: assert property (
        @(posedge clk) disable iff (rst) if_id_write_en |-> (IF_ID_next_i_addr == ($past($initstate) + 32'd4))
    );

    // pc_reg is zero on reset.
    check_pc_reg_zero_on_reset: assert property (
        @(posedge clk) rst |-> (clk ? $past(pc_reg) == 32'h00000000 : 1'b0)
    );

    // pc_reg holds its value when pc_write is low.
    check_pc_reg_holds_when_not_written: assert property (
        @(posedge clk) disable iff (rst) !pc_write |-> (clk ? $past(pc_reg) == $past(pc_reg) : 1'b0)
    );

    // pc_reg updates to the selected next value when pc_write is high.
    check_pc_reg_updates_on_write: assert property (
        @(posedge clk) disable iff (rst)
        pc_write |-> (clk ? $past(pc_reg) == ($past(pc_source) == 2'b00
                                             ? ($past($initstate) + 32'd4)
                                             : (($past(pc_source) == 2'b01) ? $past(branch_addr)
                                                                           : (($past(pc_source) == 2'b10) ? $past(jump_addr)
                                                                                                         : $past(reg_data_1))))
                          : 1'b0)
    );

endmodule