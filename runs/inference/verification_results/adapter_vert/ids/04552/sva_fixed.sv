module logic_function_sva (
    input logic A1,
    input logic A2,
    input logic B1,
    input logic B2,
    input logic C1,
    input logic Y,
    input logic nand0_out_Y,
    input logic or0_out,
    input logic or1_out,
    input logic clk_in_13
);

property ClockSynceotid; @(posedge clk_in_13) (Y) |-> (or0_out == (B2 || B1)) && (or1_out == (A2 || A1)) && (nand0_out_Y == !(or1_out && or0_out && C1)) && (Y == nand0_out_Y); endproperty
assert property (ClockSynceotid);

property SyncCheckeotid; @(posedge clk_in_13) (Y) |-> (or0_out == (B2 || B1)) && (or1_out == (A2 || A1)) && (nand0_out_Y == !(or1_out && or0_out && C1)) && (Y == nand0_out_Y); endproperty
assert property (SyncCheckeotid);

endmodule