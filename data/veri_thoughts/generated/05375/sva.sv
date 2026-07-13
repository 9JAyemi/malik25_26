module EX_stage_sva (
    input logic        clk,
    input logic        rst,
    input logic        EX_stall,
    input logic        EX_flush,
    input logic        M_stall,
    input logic        EX_regwrite,
    input logic        EX_memtoreg,
    input logic        EX_memread,
    input logic        EX_memwrite,
    input logic [31:0] EX_memaddr,
    input logic [8:0]  EX_load_op,
    input logic [5:0]  EX_store_op,
    input logic [31:0] EX_alu_out,
    input logic [31:0] EX_alu_out_t,
    input logic [4:0]  EX_rt_rd,

    input logic        M_regwrite,
    input logic        M_memtoreg,
    input logic        M_memread,
    input logic        M_memwrite,
    input logic [31:0] M_memaddr,
    input logic [8:0]  M_load_op,
    input logic [5:0]  M_store_op,
    input logic [31:0] M_alu_out,
    input logic [4:0]  M_rt_rd
);

    // Reset clears every M-stage register.
    check_reset_clears_outputs: assert property (
        @(posedge clk)
        rst |=> (M_regwrite == 1'b0 &&
                 M_memtoreg == 1'b0 &&
                 M_memread  == 1'b0 &&
                 M_memwrite == 1'b0 &&
                 M_memaddr  == 32'b0 &&
                 M_load_op  == 9'b0 &&
                 M_store_op == 6'b0 &&
                 M_alu_out  == 32'b0 &&
                 M_rt_rd    == 5'b0)
    );

    // M_stall holds all M-stage registers.
    check_m_stall_holds_outputs: assert property (
        @(posedge clk) disable iff (rst)
        M_stall |=> (M_regwrite == $past(M_regwrite) &&
                     M_memtoreg == $past(M_memtoreg) &&
                     M_memread  == $past(M_memread)  &&
                     M_memwrite == $past(M_memwrite) &&
                     M_memaddr  == $past(M_memaddr)  &&
                     M_load_op  == $past(M_load_op)  &&
                     M_store_op == $past(M_store_op) &&
                     M_alu_out  == $past(M_alu_out)  &&
                     M_rt_rd    == $past(M_rt_rd))
    );

    // Non-stalled pass-through fields always capture EX inputs.
    check_nonstalled_passthrough_fields: assert property (
        @(posedge clk) disable iff (rst)
        !M_stall |=> (M_memtoreg == $past(EX_memtoreg) &&
                      M_load_op  == $past(EX_load_op)  &&
                      M_store_op == $past(EX_store_op) &&
                      M_alu_out  == $past(EX_alu_out)  &&
                      M_rt_rd    == $past(EX_rt_rd))
    );

    // EX_stall or EX_flush inserts zeros into side-effecting controls and address.
    check_bubble_zeroes_control_and_addr: assert property (
        @(posedge clk) disable iff (rst)
        (!M_stall && (EX_stall || EX_flush)) |=> (M_regwrite == 1'b0 &&
                                                  M_memread  == 1'b0 &&
                                                  M_memwrite == 1'b0 &&
                                                  M_memaddr  == 32'b0)
    );

    // Without stalls or flushes, control signals capture EX inputs.
    check_normal_control_transfer: assert property (
        @(posedge clk) disable iff (rst)
        (!M_stall && !EX_stall && !EX_flush) |=> (M_regwrite == $past(EX_regwrite) &&
                                                  M_memread  == $past(EX_memread)  &&
                                                  M_memwrite == $past(EX_memwrite) &&
                                                  M_memaddr  == $past(EX_memaddr))
    );

    // M_stall has priority over EX_stall and EX_flush.
    check_m_stall_priority: assert property (
        @(posedge clk) disable iff (rst)
        (M_stall && (EX_stall || EX_flush)) |=> (M_regwrite == $past(M_regwrite) &&
                                                 M_memtoreg == $past(M_memtoreg) &&
                                                 M_memread  == $past(M_memread)  &&
                                                 M_memwrite == $past(M_memwrite) &&
                                                 M_memaddr  == $past(M_memaddr)  &&
                                                 M_load_op  == $past(M_load_op)  &&
                                                 M_store_op == $past(M_store_op) &&
                                                 M_alu_out  == $past(M_alu_out)  &&
                                                 M_rt_rd    == $past(M_rt_rd))
    );

endmodule