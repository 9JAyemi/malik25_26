module EX_ME_sva (
    input logic        clk,
    input logic        rst,
    input logic [31:0] ex_aluresult,
    input logic [4:0]  ex_td,
    input logic [31:0] ex_d2,
    input logic        ex_WREG,
    input logic        ex_WMEM,
    input logic        ex_LW,
    input logic [31:0] ex_instr,
    input logic [31:0] me_aluresult,
    input logic [4:0]  me_td,
    input logic [31:0] me_d2,
    input logic        me_WREG,
    input logic        me_WMEM,
    input logic        me_LW,
    input logic [31:0] me_instr
);

    // Outputs go to their reset values after a reset cycle.
    check_reset_values: assert property (
        @(posedge clk)
        rst |=> (me_aluresult == 32'd0 &&
                 me_d2        == 32'd0 &&
                 me_td        == 5'd0  &&
                 me_WREG      == 1'b0  &&
                 me_WMEM      == 1'b0  &&
                 me_LW        == 1'b0  &&
                 me_instr     == 32'b100000)
    );

    // Data-path registers capture the EX-stage values on each clock.
    check_data_capture: assert property (
        @(posedge clk) disable iff (rst)
        1'b1 |=> (me_aluresult == $past(ex_aluresult) &&
                  me_d2        == $past(ex_d2) &&
                  me_td        == $past(ex_td))
    );

    // Control registers capture the EX-stage control bits on each clock.
    check_control_capture: assert property (
        @(posedge clk) disable iff (rst)
        1'b1 |=> (me_WREG == $past(ex_WREG) &&
                  me_WMEM == $past(ex_WMEM) &&
                  me_LW   == $past(ex_LW))
    );

    // The instruction register captures the EX-stage instruction on each clock.
    check_instr_capture: assert property (
        @(posedge clk) disable iff (rst)
        1'b1 |=> (me_instr == $past(ex_instr))
    );

endmodule