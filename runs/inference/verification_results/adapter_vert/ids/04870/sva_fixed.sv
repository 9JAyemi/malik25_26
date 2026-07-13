module logical_and_sva (
    input logic A,
    input logic B,
    input logic C,
    input logic Y,
    input logic clk_in_1
);

property SyncIneotid; @(posedge clk_in_1) (A) && (B) && (C) |-> (Y) ;endproperty
assert property (SyncIneotid);

property SyncCheckeotid; @(posedge clk_in_1) (A) && (B) && (!C) |-> !(Y) ;endproperty
assert property (SyncCheckeotid);

property SyncCheckeotid_2; @(posedge clk_in_1) (A) && (!B) && (C) |-> !(Y) ;endproperty
assert property (SyncCheckeotid_2);

property SyncCheckeotid_3; @(posedge clk_in_1) (!A) && (B) && (C) |-> !(Y) ;endproperty
assert property (SyncCheckeotid_3);

endmodule