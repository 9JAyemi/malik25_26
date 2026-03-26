module EX_ME_sva (
    input logic        clk,
    input logic        rst,
    input logic        stall,
    input logic [31:0] ex_aluresult,
    input logic [4:0]  ex_td,
    input logic [31:0] ex_d2,
    input logic        ex_WREG,
    input logic        ex_WMEM,
    input logic        ex_LW,
    input logic [31:0] ex_instr,
    input logic [31:0] ex_pc,
    input logic [31:0] me_aluresult,
    input logic [4:0]  me_td,
    input logic [31:0] me_d2,
    input logic        me_WREG,
    input logic        me_WMEM,
    input logic        me_LW,
    input logic [31:0] me_instr,
    input logic [31:0] me_pc
);

    // Reset drives all ME-stage registers to their defined reset values.
    check_reset_values: assert property (
        @(posedge clk)
        rst |-> (me_aluresult == 32'b0) &&
               (me_d2        == 32'b0) &&
               (me_td        == 5'b0)  &&
               (me_WREG      == 1'b0)  &&
               (me_WMEM      == 1'b0)  &&
               (me_LW        == 1'b0)  &&
               (me_instr     == 32'b100000) &&
               (me_pc        == 32'b0)
    );

    // Stall inserts a bubble into the data, destination, and control fields.
    check_stall_bubble_fields: assert property (
        @(posedge clk) disable iff (rst)
        stall |=> ((me_aluresult == 32'b0) &&
                   (me_d2        == 32'b0) &&
                   (me_td        == 5'b0)  &&
                   (me_WREG      == 1'b0)  &&
                   (me_WMEM      == 1'b0)  &&
                   (me_LW        == 1'b0)  &&
                   (me_instr     == 32'b100000))
    );

    // Stall still forwards ex_pc because the later assignment overrides the zero write.
    check_stall_forwards_pc: assert property (
        @(posedge clk) disable iff (rst)
        stall |=> (me_pc == $past(ex_pc))
    );

    // Without stall, the ALU result is registered into the ME stage.
    check_pass_aluresult: assert property (
        @(posedge clk) disable iff (rst)
        !stall |=> (me_aluresult == $past(ex_aluresult))
    );

    // Without stall, store data and destination register are registered.
    check_pass_d2_td: assert property (
        @(posedge clk) disable iff (rst)
        !stall |=> ((me_d2 == $past(ex_d2)) &&
                    (me_td == $past(ex_td)))
    );

    // Without stall, the writeback and memory control bits are registered.
    check_pass_controls: assert property (
        @(posedge clk) disable iff (rst)
        !stall |=> ((me_WREG == $past(ex_WREG)) &&
                    (me_WMEM == $past(ex_WMEM)) &&
                    (me_LW   == $past(ex_LW)))
    );

    // Without stall, the instruction is registered into the ME stage.
    check_pass_instr: assert property (
        @(posedge clk) disable iff (rst)
        !stall |=> (me_instr == $past(ex_instr))
    );

    // Without stall, the PC is registered into the ME stage.
    check_pass_pc: assert property (
        @(posedge clk) disable iff (rst)
        !stall |=> (me_pc == $past(ex_pc))
    );

endmodule