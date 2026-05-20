module mux4_sva (
    input logic A0,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic S1,
    input logic SA,
    input logic X,
    input logic SB,
    input logic SC,
    input logic SD,
    input logic SE,
    input logic SF,
    input logic SG,
    input logic SH,
    input logic clk_in_1
);

property ClockSynceotid; @(posedge clk_in_1) (A0) |-> (SA) ; endproperty
assert property (ClockSynceotid);

property ClockSynceotid_2; @(posedge clk_in_1) (A1) |-> (SB) ; endproperty
assert property (ClockSynceotid_2);

property ClockSynceotid_3; @(posedge clk_in_1) (A2) |-> (SC) ; endproperty
assert property (ClockSynceotid_3);

property ClockSynceotid_4; @(posedge clk_in_1) (A3) |-> (SD) ; endproperty
assert property (ClockSynceotid_4);

property ValidSynceotid; @(posedge clk_in_1) (SA) ||  (SB)  |-> (SE) ; endproperty
assert property (ValidSynceotid);

property ValidSynceotid_2; @(posedge clk_in_1) (SC) ||  (SD)  |-> (SF) ; endproperty
assert property (ValidSynceotid_2);

property SyncCheckeotid; @(posedge clk_in_1) (SE) &&  ( !S1 )  |-> (SG) ; endproperty
assert property (SyncCheckeotid);

property SyncCheckeotid_2; @(posedge clk_in_1) (SF) &&  ( S1 )  |-> (SH) ; endproperty
assert property (SyncCheckeotid_2);

property SyncCheckeotid_3; @(posedge clk_in_1)  (SG)  ||  (SH)  ==  (X) ; endproperty
assert property (SyncCheckeotid_3);

endmodule