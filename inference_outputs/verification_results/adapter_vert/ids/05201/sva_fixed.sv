module binary_adder_sva (
    input logic A,
    input logic B,
    input logic Cin,
    input logic Cout,
    input logic En,
    input logic S,
    input logic clk_in_1
);

property SyncAddOneeotid; @(posedge clk_in_1) (A) |-> (S) ;endproperty
assert property (SyncAddOneeotid);

property SyncCarryeotid; @(posedge clk_in_1) (A) &&  (B) &&  (Cin) |-> (Cout) ;endproperty
assert property (SyncCarryeotid);

property SyncAdderCheckeotid; @(posedge clk_in_1) (A) &&  (B) &&  (Cin) &&  (En) |-> (S) ;endproperty
assert property (SyncAdderCheckeotid);

endmodule