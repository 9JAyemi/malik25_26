module logic_gate_sva (
    input logic A1,
    input logic A2,
    input logic B1,
    input logic C1,
    input logic D1,
    input logic X,
    input logic clk_in_19
);

property ClockSynceotid; @(posedge clk_in_19) (A1) == (1) &&  (A2) == (0) &&  (B1) == (1) &&  (C1) == (0) &&  (D1) == (1) |-> (X) == 1 ;endproperty
assert property (ClockSynceotid);

property SyncCheckeotid; @(posedge clk_in_19) (A1) == (1) &&  (A2) == (0) &&  (B1) != 1 &&  (C1) != 0 &&  (D1) != 1 |-> (X) == 0 ;endproperty
assert property (SyncCheckeotid);

property SyncCheckeotid_2; @(posedge clk_in_19) (A1) != 1 ||  (A2) != 0 ||  (B1) != 1 ||  (C1) != 0 ||  (D1) != 1 |-> (X) == 0 ;endproperty
assert property (SyncCheckeotid_2);

endmodule