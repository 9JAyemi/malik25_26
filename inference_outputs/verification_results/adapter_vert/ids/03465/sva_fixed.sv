module sky130_fd_sc_hvl__a22o_sva (
    input logic A1,
    input logic A2,
    input logic B1,
    input logic B2,
    input logic X,
    input logic clock_div_13
);

property ClockSynceotid; @(posedge clock_div_13) (A1) && (A2) && ! (B1) && ! (B2) |-> (X) ; endproperty
assert property (ClockSynceotid);

property SyncCheckeotid; @(posedge clock_div_13) ! (A1) && ! (A2) &&  (B1) &&  (B2) |-> (X) ; endproperty
assert property (SyncCheckeotid);

property ClockSynceotid_2; @(posedge clock_div_13) (A1) && (A2) && ! (B1) && ! (B2) || ! (A1) && ! (A2) &&  (B1) &&  (B2) |->  (X)  ; endproperty
assert property (ClockSynceotid_2);

endmodule