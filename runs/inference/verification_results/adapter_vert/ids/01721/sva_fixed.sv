module and_gate_4_sva (
    input logic A1,
    input logic A2,
    input logic A3,
    input logic B1,
    input logic C1,
    input logic Y,
    input logic temp1,
    input logic clk_in_1,
    input logic temp2,
    input logic temp3
);

property SyncIneotid; @(posedge clk_in_1) (A1) && (A2) |-> (temp1) ;endproperty
assert property (SyncIneotid);

property SyncCheckeotid; @(posedge clk_in_1) (A1) && (A2) && (A3) |-> (temp2) ;endproperty
assert property (SyncCheckeotid);

property SyncCheckeotid_2; @(posedge clk_in_1) (A1) && (A2) && (A3) && (B1) |-> (temp3) ;endproperty
assert property (SyncCheckeotid_2);

property ValidSynceotid; @(posedge clk_in_1) (A1) && (A2) && (A3) && (B1) && (C1) |-> (Y) ;endproperty
assert property (ValidSynceotid);

endmodule