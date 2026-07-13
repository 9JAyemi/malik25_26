module sky130_fd_sc_ls__ha_sva (
    input logic A,
    input logic B,
    input logic COUT,
    input logic SUM,
    input logic and0_out_COUT,
    input logic xor0_out_SUM,
    input logic clock_div_19
);

property ClockSynceotid; @(posedge clock_div_19) (COUT) |-> (and0_out_COUT) ;endproperty
assert property (ClockSynceotid);

property ClockSynceotid_2; @(posedge clock_div_19) (and0_out_COUT) |-> (COUT) ;endproperty
assert property (ClockSynceotid_2);

property SyncCheckeotid; @(posedge clock_div_19) (B) != (A) |-> (xor0_out_SUM) ;endproperty
assert property (SyncCheckeotid);

property SyncCheckeotid_2; @(posedge clock_div_19) (xor0_out_SUM) |-> (SUM) ;endproperty
assert property (SyncCheckeotid_2);

endmodule