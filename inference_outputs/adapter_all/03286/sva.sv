module EX_ME_sva (
    input logic clk,
    input logic rst,
    input logic [31:0] ex_aluresult,
    input logic [4:0] ex_td,
    input logic [31:0] ex_d2,
    input logic ex_WREG,
    input logic ex_WMEM,
    input logic ex_LW,
    input logic [31:0] ex_instr,
    input logic [31:0] me_aluresult,
    input logic [4:0] me_td,
    input logic [31:0] me_d2,
    input logic me_WREG,
    input logic me_WMEM,
    input logic me_LW,
    input logic [31:0] me_instr
);
    ///// Reset behavior /////
    // On reset assertion, all ME registers must be zero.
    reset_clears_me_regs: assert property (
        @(posedge clk) rst |-> (me_aluresult == 32'd0) && (me_d2 == 32'd0) && (me_td == 5'd0) &&
                               (me_WREG == 1'b0) && (me_WMEM == 1'b0) && (me_LW == 1'b0) &&
                               (me_instr == 32'h00000000)
    );

    // On reset assertion, me_instr must be 32'h00000000.
    reset_me_instr_zero: assert property (
        @(posedge clk) rst |-> (me_instr == 32'h00000000)
    );

    ///// Pipeline register behavior /////
    // me_aluresult captures ex_aluresult on the next cycle (when not in reset).
    pipe_aluresult: assert property (
        @(posedge clk) disable iff (rst) 1'b1 |=> (me_aluresult == $past(ex_aluresult))
    );

    // me_d2 captures ex_d2 on the next cycle (when not in reset).
    pipe_d2: assert property (
        @(posedge clk) disable iff (rst) 1'b1 |=> (me_d2 == $past(ex_d2))
    );

    // me_td captures ex_td on the next cycle (when not in reset).
    pipe_td: assert property (
        @(posedge clk) disable iff (rst) 1'b1 |=> (me_td == $past(ex_td))
    );

    // me_WREG captures ex_WREG on the next cycle (when not in reset).
    pipe_WREG: assert property (
        @(posedge clk) disable iff (rst) 1'b1 |=> (me_WREG == $past(ex_WREG))
    );

    // me_WMEM captures ex_WMEM on the next cycle (when not in reset).
    pipe_WMEM: assert property (
        @(posedge clk) disable iff (rst) 1'b1 |=> (me_WMEM == $past(ex_WMEM))
    );

    // me_LW captures ex_LW on the next cycle (when not in reset).
    pipe_LW: assert property (
        @(posedge clk) disable iff (rst) 1'b1 |=> (me_LW == $past(ex_LW))
    );

    // me_instr captures ex_instr on the next cycle (when not in reset).
    pipe_instr: assert property (
        @(posedge clk) disable iff (rst) 1'b1 |=> (me_instr == $past(ex_instr))
    );

    ///// Combinational next-state relation /////
    // me_aluresult equals ex_aluresult from the previous cycle (when not in reset).
    next_aluresult: assert property (
        @(posedge clk) disable iff (rst) 1'b1 |-> (me_aluresult == $past(ex_aluresult))
    );

    // me_d2 equals ex_d2 from the previous cycle (when not in reset).
    next_d2: assert property (
        @(posedge clk) disable iff (rst) 1'b1 |-> (me_d2 == $past(ex_d2))
    );

    // me_td equals ex_td from the previous cycle (when not in reset).
    next_td: assert property (
        @(posedge clk) disable iff (rst) 1'b1 |-> (me_td == $past(ex_td))
    );

    // me_WREG equals ex_WREG from the previous cycle (when not in reset).
    next_WREG: assert property (
        @(posedge clk) disable iff (rst) 1'b1 |-> (me_WREG == $past(ex_WREG))
    );

    // me_WMEM equals ex_WMEM from the previous cycle (when not in reset).
    next_WMEM: assert property (
        @(posedge clk) disable iff (rst) 1'b1 |-> (me_WMEM == $past(ex_WMEM))
    );

    // me_LW equals ex_LW from the previous cycle (when not in reset).
    next_LW: assert property (
        @(posedge clk) disable iff (rst) 1'b1 |-> (me_LW == $past(ex_LW))
    );

    // me_instr equals ex_instr from the previous cycle (when not in reset).
    next_instr: assert property (
        @(posedge clk) disable iff (rst) 1'b1 |-> (me_instr == $past(ex_instr))
    );
endmodule