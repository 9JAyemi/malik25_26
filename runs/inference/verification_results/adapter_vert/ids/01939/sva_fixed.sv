module my_module_sva (
    input logic A1,
    input logic A2,
    input logic B1,
    input logic B2,
    input logic X,
    input logic and1_out,
    input logic and2_out,
    input logic not1_out,
    input logic clk_in_1
);

property SyncCheckeotid; @(posedge clk_in_1) (A1) && (A2) |-> (and1_out) ;endproperty
assert property (SyncCheckeotid);

property SyncCheckeotid_2; @(posedge clk_in_1) (B1) && (B2) |-> (and2_out) ;endproperty
assert property (SyncCheckeotid_2);

property SyncCheckeotid_3; @(posedge clk_in_1) (B1) && (B2) |-> (not1_out) ;endproperty
assert property (SyncCheckeotid_3);

property SyncCheckeotid_4; @(posedge clk_in_1) (A1) && (A2) &&  (B1) && (B2)  |-> (X) == (and1_out && not1_out) ;endproperty
assert property (SyncCheckeotid_4);

endmodule