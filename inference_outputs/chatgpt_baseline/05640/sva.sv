module if_stage_sva(
    input logic        clk,
    input logic        rst,
    input logic        if_id_write_en,
    input logic        pc_write,
    input logic [1:0]  pc_source,
    input logic        pstop_i,
    input logic        i_read_en,
    input logic [31:0] i_addr,
    input logic [31:0] i_instr_in,
    input logic [31:0] jump_addr,
    input logic [31:0] branch_addr,
    input logic [31:0] reg_data_1,
    input logic [31:0] IF_ID_next_i_addr,
    input logic [31:0] IF_ID_instruction
);

    wire mem_op = (IF_ID_instruction[31:26] == 6'b100011) ||
                  (IF_ID_instruction[31:26] == 6'b101011);

    // Reset drives the visible state registers to zero.
    check_reset_clears_state: assert property (
        @(posedge clk)
        rst |=> ((i_addr == 32'd0) &&
                 (IF_ID_next_i_addr == 32'd0) &&
                 (IF_ID_instruction == 32'd0))
    );

    // Instruction read enable is permanently asserted.
    check_read_enable_high: assert property (
        @(posedge clk) disable iff (rst)
        (i_read_en == 1'b1)
    );

    // Right shift by two keeps the top two address bits at zero.
    check_i_addr_upper_bits_zero: assert property (
        @(posedge clk) disable iff (rst)
        (i_addr[31:30] == 2'b00)
    );

    // PC-derived address holds when PC write is blocked.
    check_pc_holds_without_enabled_update: assert property (
        @(posedge clk) disable iff (rst)
        (!pc_write || pstop_i || mem_op)
        |=> (i_addr == $past(i_addr))
    );

    // Sequential PC selection increments the word address by one.
    check_pc_uses_sequential_next_addr: assert property (
        @(posedge clk) disable iff (rst)
        (pc_write && !pstop_i && !mem_op && (pc_source == 2'b00))
        |=> (i_addr[29:0] == ($past(i_addr[29:0]) + 30'd1))
    );

    // Branch PC selection loads branch_addr into the PC.
    check_pc_uses_branch_addr: assert property (
        @(posedge clk) disable iff (rst)
        (pc_write && !pstop_i && !mem_op && (pc_source == 2'b01))
        |=> (i_addr == ($past(branch_addr) >> 2))
    );

    // Jump PC selection loads jump_addr into the PC.
    check_pc_uses_jump_addr: assert property (
        @(posedge clk) disable iff (rst)
        (pc_write && !pstop_i && !mem_op && (pc_source == 2'b10))
        |=> (i_addr == ($past(jump_addr) >> 2))
    );

    // Register PC selection loads reg_data_1 into the PC.
    check_pc_uses_reg_data_1: assert property (
        @(posedge clk) disable iff (rst)
        (pc_write && !pstop_i && !mem_op && (pc_source == 2'b11))
        |=> (i_addr == ($past(reg_data_1) >> 2))
    );

    // IF/ID registers hold when write enable is low.
    check_ifid_holds_without_write_enable: assert property (
        @(posedge clk) disable iff (rst)
        (!if_id_write_en)
        |=> ((IF_ID_next_i_addr == $past(IF_ID_next_i_addr)) &&
             (IF_ID_instruction == $past(IF_ID_instruction)))
    );

    // IF/ID next address captures pc_reg + 4 when write enabled.
    check_ifid_captures_next_addr_upper_bits: assert property (
        @(posedge clk) disable iff (rst)
        if_id_write_en
        |=> (IF_ID_next_i_addr[31:2] == ($past(i_addr[29:0]) + 30'd1))
    );

    // IF/ID instruction captures the incoming instruction when not stopped.
    check_ifid_captures_instruction_when_not_stopped: assert property (
        @(posedge clk) disable iff (rst)
        (if_id_write_en && !pstop_i && !mem_op)
        |=> (IF_ID_instruction == $past(i_instr_in))
    );

    // IF/ID instruction is cleared when stopped by pstop_i or mem_op.
    check_ifid_zeros_instruction_when_stopped: assert property (
        @(posedge clk) disable iff (rst)
        (if_id_write_en && (pstop_i || mem_op))
        |=> (IF_ID_instruction == 32'd0)
    );

endmodule