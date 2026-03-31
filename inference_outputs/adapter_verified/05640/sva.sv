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

// i_read_en is permanently asserted high.
    check_i_read_en_high: assert property (
        @(posedge clk) disable iff (rst) i_read_en == 1'b1
    );

// i_addr is the current PC divided by 4.
    check_i_addr_div_by_4: assert property (
        @(posedge clk) disable iff (rst) i_addr == (pc_reg >> 2)
    );

// IF_ID_next_i_addr captures the next PC value on the next cycle.
    check_next_i_addr_capture: assert property (
        @(posedge clk) disable iff (rst) 1'b1 |=> (IF_ID_next_i_addr == next_i_addr)
    );

// IF_ID_instruction captures the next instruction on the next cycle.
    check_instruction_capture: assert property (
        @(posedge clk) disable iff (rst) 1'b1 |=> (IF_ID_instruction == next_instruction)
    );

// With write enable, IF_ID_next_i_addr loads next_i_addr.
    check_next_i_addr_write_enable: assert property (
        @(posedge clk) disable iff (rst) if_id_write_en |=> (IF_ID_next_i_addr == next_i_addr)
    );

// With write enable, IF_ID_instruction loads next_instruction.
    check_instruction_write_enable: assert property (
        @(posedge clk) disable iff (rst) if_id_write_enable |=> (IF_ID_instruction == next_instruction)
    );

// Without write enable, IF_ID_next_i_addr holds its value.
    check_next_i_addr_hold: assert property (
        @(posedge clk) disable iff (rst) !if_id_write_en |=> (IF_ID_next_i_addr == $past(IF_ID_next_i_addr))
    );

// Without write enable, IF_ID_instruction holds its value.
    check_instruction_hold: assert property (
        @(posedge clk) disable iff (rst) !if_id_write_enable |=> (IF_ID_instruction == $past(IF_ID_instruction))
    );

// With write enable and no stop or memory operation, IF_ID_instruction loads i_instr_in.
    check_instruction_load_data: assert property (
        @(posedge clk) disable iff (rst) (if_id_write_en && !(pstop_i || mem_op)) |=> (IF_ID_instruction == i_instr_in)
    );

// With write enable and stop or memory operation, IF_ID_instruction clears to zero.
    check_instruction_clear_on_stop_or_memop: assert property (
        @(posedge clk) disable iff (rst) (if_id_write_en && (pstop_i || mem_op)) |=> (IF_ID_instruction == 32'h0)
    );

// With write enable and no stop or memory operation, IF_ID_next_i_addr loads next_i_addr.
    check_next_i_addr_load_on_write: assert property (
        @(posedge clk) disable iff (rst) (if_id_write_en && !(pstop_i || mem_op)) |=> (IF_ID_next_i_addr == next_i_addr)
    );

// With write enable and stop or memory operation, IF_ID_next_i_addr clears to zero.
    check_next_i_addr_clear_on_stop_or_memop: assert property (
        @(posedge clk) disable iff (rst) (if_id_write_en && (pstop_i || mem_op)) |=> (IF_ID_next_i_addr == 32'h0)
    );

endmodule
