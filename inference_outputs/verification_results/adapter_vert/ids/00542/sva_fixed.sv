module my_module_sva (
    input logic A1,
    input logic A2,
    input logic A3,
    input logic B1,
    input logic X,
    input logic and0_out,
    input logic or0_out_X,
    input logic clk_osc_14
);

property ClockSynceotid; @(posedge clk_osc_14) (and0_out) == (A3 & A1 & A2) ; endproperty
assert property (ClockSynceotid);

property SyncOkeotid; @(posedge clk_osc_14) (or0_out_X) == (and0_out | B1) ; endproperty
assert property (SyncOkeotid);

property PowerSynceotid; @(posedge clk_osc_14) (X) == (or0_out_X) ; endproperty
assert property (PowerSynceotid);

endmodule