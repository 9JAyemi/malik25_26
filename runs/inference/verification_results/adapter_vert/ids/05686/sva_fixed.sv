module sky130_fd_sc_hs__a222o_sva (
    input logic A1,
    input logic A2,
    input logic B1,
    input logic B2,
    input logic C1,
    input logic C2,
    input logic X,
    input logic b0,
    input logic b1,
    input logic clk_osc_15
);

property ClockSynceotid; @(posedge clk_osc_15) (A1) && (A2) &&  (B1) && (B2) |-> (X) == 1'b1 ;endproperty
assert property (ClockSynceotid);

property SyncCheckeotid; @(posedge clk_osc_15) (A1) && (A2) &&  !(B1) && !(B2)  &&  !(C1) &&  !(C2)  |-> (X) == 1'b1 ;endproperty
assert property (SyncCheckeotid);

property SyncCheckeotid_2; @(posedge clk_osc_15) !(A1) && !(A2)  &&  (B1) && (B2) |-> (X) == 1'b1 ;endproperty
assert property (SyncCheckeotid_2);

property SyncCheckeotid_3; @(posedge clk_osc_15) !(A1) && !(A2)  &&  !(B1) && !(B2)  &&  (C1) &&  (C2)  |-> (X) == 1'b0 ;endproperty
assert property (SyncCheckeotid_3);

endmodule