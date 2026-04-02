module EX_ME_assertions (
    input logic clk,
    input logic rst,
    input logic [31:0] ex_aluresult, ex_d2, ex_instr,
    input logic [4:0] ex_td,
    input logic ex_WREG, ex_WMEM, ex_LW,
    output logic [31:0] me_aluresult, me_d2, me_instr,
    output logic [4:0] me_td,
    output logic me_WREG, me_WMEM, me_LW
);
    // Reset behavior: At reset, all outputs should be zero
    reset: assert property (
        @(posedge clk) disable iff (!rst) (me_aluresult == 32'b0) && (me_d2 == 32'b0) && (me_td == 5'b0) && (me_WREG == 1'b0) && (me_WMEM == 1'b0) && (me_LW == 1'b0) && (me_instr == 32'b100000)
    );

    // Sequential behavior: Outputs should match inputs at the next clock edge
    sequential_behavior: assert property (
        @(posedge clk) disable iff (!rst) (me_aluresult == ex_aluresult) && (me_d2 == ex_d2) && (me_td == ex_td) && (me_WREG == ex_WREG) && (me_WMEM == ex_WMEM) && (me_LW == ex_LW) && (me_instr == ex_instr)
    );

endmodule