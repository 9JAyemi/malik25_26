module EX_ME_sva (
    input logic clk,
    input logic rst,
    input logic [31:0] ex_aluresult,
    input logic [31:0] ex_d2,
    input logic [4:0]  ex_td,
    input logic        ex_WREG,
    input logic        ex_WMEM,
    input logic        ex_LW,
    input logic [31:0] ex_instr,
    input logic [31:0] me_aluresult,
    input logic [31:0] me_d2,
    input logic [4:0]  me_td,
    input logic        me_WREG,
    input logic        me_WMEM,
    input logic        me_LW,
    input logic [31:0] me_instr
);

    // Reset clears all stored outputs.
    check_reset_clears_outputs: assert property (
        @(posedge clk)
        rst |-> ((me_aluresult == 32'd0) &&
                 (me_d2         == 32'd0) &&
                 (me_td         == 5'd0)  &&
                 (me_WREG       == 1'b0)  &&
                 (me_WMEM       == 1'b0)  &&
                 (me_LW         == 1'b0)  &&
                 (me_instr      == 32'h20))
    );

    // me_aluresult captures ex_aluresult on each non-reset cycle.
    check_aluresult_captured: assert property (
        @(posedge clk) disable iff (rst)
        1'b1 |=> (me_aluresult == $past(ex_aluresult))
    );

    // me_d2 captures ex_d2 on each non-reset cycle.
    check_d2_captured: assert property (
        @(posedge clk) disable iff (rst)
        1'b1 |=> (me_d2 == $past(ex_d2))
    );

    // me_td captures ex_td on each non-reset cycle.
    check_td_captured: assert property (
        @(posedge clk) disable iff (rst)
        1'b1 |=> (me_td == $past(ex_td))
    );

    // me_WREG captures ex_WREG on each non-reset cycle.
    check_wreg_captured: assert property (
        @(posedge clk) disable iff (rst)
        1'b1 |=> (me_WREG == $past(ex_WREG))
    );

    // me_WMEM captures ex_WMEM on each non-reset cycle.
    check_wmem_captured: assert property (
        @(posedge clk) disable iff (rst)
        1'b1 |=> (me_WMEM == $past(ex_WMEM))
    );

    // me_LW captures ex_LW on each non-reset cycle.
    check_lw_captured: assert property (
        @(posedge clk) disable iff (rst)
        1'b1 |=> (me_LW == $past(ex_LW))
    );

    // me_instr captures ex_instr on each non-reset cycle.
    check_instr_captured: assert property (
        @(posedge clk) disable iff (rst)
        1'b1 |=> (me_instr == $past(ex_instr))
    );

endmodule