module and4_pwr_good_sva (
    input logic A_N,
    input logic B,
    input logic C,
    input logic D,
    input logic VGND,
    input logic VPWR,
    input logic X,
    input logic and0_out_X,
    input logic not0_out,
    input logic pwrgood_pp0_out_X,
    input logic clk_osc_19
);

property ClockSynceotid; @(posedge clk_osc_19) (A_N) |-> not0_out ;endproperty
assert property (ClockSynceotid);

property SyncCheckeotid; @(posedge clk_osc_19) (B) && @(posedge clk_osc_19) (C) && @(posedge clk_osc_19) (D) |-> and0_out_X ;endproperty
assert property (SyncCheckeotid);

property PowerSynceotid; @(posedge clk_osc_19) (and0_out_X) && @(posedge clk_osc_19) (VPWR) && @(posedge clk_osc_19) (VGND) |-> pwrgood_pp0_out_X ;endproperty
assert property (PowerSynceotid);

property ValidOuteotid; @(posedge clk_osc_19) (pwrgood_pp0_out_X) |-> X ;endproperty
assert property (ValidOuteotid);

endmodule