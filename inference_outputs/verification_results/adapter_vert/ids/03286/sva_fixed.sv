module EX_ME_sva (
    input logic clk,
    input logic ex_LW,
    input logic ex_WMEM,
    input logic ex_WREG,
    input logic ex_aluresult,
    input logic ex_d2,
    input logic ex_instr,
    input logic ex_td,
    input logic me_LW,
    input logic me_WMEM,
    input logic me_WREG,
    input logic me_aluresult,
    input logic me_d2,
    input logic me_instr,
    input logic me_td,
    input logic rst,
    input logic b100000
);

property ResetSynceotid; @(posedge clk) (rst) |-> (me_aluresult == 0) && (me_d2 == 0) && (me_td == 0) && (me_WREG == 0) && (me_WMEM == 0) && (me_LW == 0) && (me_instr == 32'b100000) ;endproperty
assert property (ResetSynceotid);

property SyncLoadeotid; @(posedge clk) ( !rst ) |-> (me_aluresult == ex_aluresult) && (me_d2 == ex_d2) && (me_td == ex_td) && (me_WREG == ex_WREG) && (me_WMEM == ex_WMEM) && (me_LW == ex_LW) && (me_instr == ex_instr) ;endproperty
assert property (SyncLoadeotid);

endmodule