module EX_ME_sva (
    input logic clk,
    input logic rst,
    input logic [31:0] ex_aluresult,
    input logic [31:0] ex_d2,
    input logic [4:0] ex_td,
    input logic ex_WREG,
    input logic ex_WMEM,
    input logic ex_LW,
    input logic [31:0] ex_instr,
    input logic [31:0] me_aluresult,
    input logic [31:0] me_d2,
    input logic [4:0] me_td,
    input logic me_WREG,
    input logic me_WMEM,
    input logic me_LW,
    input logic [31:0] me_instr
);

// Reset clears all ME stage registers and sets me_instr to 32'b100000.
    check_reset_clears_outputs: assert property (
        @(posedge clk) rst |-> (me_aluresult == 32'h0) &&
                             (me_d2 == 32'h0) &&
                             (me_td == 5'h0) &&
                             (me_WREG == 1'b0) &&
                             (me_WMEM == 1'b0) &&
                             (me_LW == 1'b0) &&
                             (me_instr == 32'h100000)
    );

// me_aluresult captures ex_aluresult on the next cycle.
    check_aluresult_pipeline: assert property (
        @(posedge clk) disable iff (rst) 1'b1 |=> (me_aluresult == $past(ex_aluresult))
    );

// me_d2 captures ex_d2 on the next cycle.
    check_d2_pipeline: assert property (
        @(posedge clk) disable iff (rst) 1'b1 |=> (me_d2 == $past(ex_d2))
    );

// me_td captures ex_td on the next cycle.
    check_td_pipeline: assert property (
        @(posedge clk) disable iff (rst) 1'b1 |=> (me_td == $past(ex_td))
    );

// me_WREG captures ex_WREG on the next cycle.
    check_wreg_pipeline: assert property (
        @(posedge clk) disable iff (rst) 1'b1 |=> (me_WREG == $past(ex_WREG))
    );

// me_WMEM captures ex_WMEM on the next cycle.
    check_wmem_pipeline: assert property (
        @(posedge clk) disable iff (rst) 1'b1 |=> (me_WMEM == $past(ex_WMEM))
    );

// me_LW captures ex_LW on the next cycle.
    check_lw_pipeline: assert property (
        @(posedge clk) disable iff (rst) 1'b1 |=> (me_LW == $past(ex_LW))
    );

// me_instr captures ex_instr on the next cycle.
    check_instr_pipeline: assert property (
        @(posedge clk) disable iff (rst) 1'b1 |=> (me_instr == $past(ex_instr))
    );

endmodule
