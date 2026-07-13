module musb_memwb_register_sva (
    input  logic        clk,
    input  logic        rst,
    input  logic [31:0] mem_read_data,
    input  logic [31:0] mem_alu_data,
    input  logic [4:0]  mem_gpr_wa,
    input  logic        mem_mem_to_gpr_select,
    input  logic        mem_gpr_we,
    input  logic        mem_flush,
    input  logic        mem_stall,
    input  logic        wb_stall,
    input  logic [31:0] wb_read_data,
    input  logic [31:0] wb_alu_data,
    input  logic [4:0]  wb_gpr_wa,
    input  logic        wb_mem_to_gpr_select,
    input  logic        wb_gpr_we
);

    // wb_read_data captures mem_read_data when WB is not stalled.
    check_wb_read_data_load: assert property (
        @(posedge clk) disable iff (rst)
        !wb_stall |=> (wb_read_data == $past(mem_read_data))
    );

    // wb_read_data holds its value during WB stall.
    check_wb_read_data_hold: assert property (
        @(posedge clk) disable iff (rst)
        wb_stall |=> (wb_read_data == $past(wb_read_data))
    );

    // wb_alu_data captures mem_alu_data when WB is not stalled.
    check_wb_alu_data_load: assert property (
        @(posedge clk) disable iff (rst)
        !wb_stall |=> (wb_alu_data == $past(mem_alu_data))
    );

    // wb_alu_data holds its value during WB stall.
    check_wb_alu_data_hold: assert property (
        @(posedge clk) disable iff (rst)
        wb_stall |=> (wb_alu_data == $past(wb_alu_data))
    );

    // wb_gpr_wa captures mem_gpr_wa when WB is not stalled.
    check_wb_gpr_wa_load: assert property (
        @(posedge clk) disable iff (rst)
        !wb_stall |=> (wb_gpr_wa == $past(mem_gpr_wa))
    );

    // wb_gpr_wa holds its value during WB stall.
    check_wb_gpr_wa_hold: assert property (
        @(posedge clk) disable iff (rst)
        wb_stall |=> (wb_gpr_wa == $past(wb_gpr_wa))
    );

    // wb_mem_to_gpr_select captures the MEM select when WB is not stalled.
    check_wb_mem_to_gpr_select_load: assert property (
        @(posedge clk) disable iff (rst)
        !wb_stall |=> (wb_mem_to_gpr_select == $past(mem_mem_to_gpr_select))
    );

    // wb_mem_to_gpr_select holds its value during WB stall.
    check_wb_mem_to_gpr_select_hold: assert property (
        @(posedge clk) disable iff (rst)
        wb_stall |=> (wb_mem_to_gpr_select == $past(wb_mem_to_gpr_select))
    );

    // wb_gpr_we holds its value during WB stall.
    check_wb_gpr_we_hold: assert property (
        @(posedge clk) disable iff (rst)
        wb_stall |=> (wb_gpr_we == $past(wb_gpr_we))
    );

    // wb_gpr_we clears when MEM stalls or flushes and WB is not stalled.
    check_wb_gpr_we_clear_on_mem_stall_or_flush: assert property (
        @(posedge clk) disable iff (rst)
        (!wb_stall && (mem_stall || mem_flush)) |=> (wb_gpr_we == 1'b0)
    );

    // wb_gpr_we captures mem_gpr_we when no stall or flush blocks it.
    check_wb_gpr_we_load: assert property (
        @(posedge clk) disable iff (rst)
        (!wb_stall && !mem_stall && !mem_flush) |=> (wb_gpr_we == $past(mem_gpr_we))
    );

endmodule