module and3_not_A_sva (
    input logic A,
    input logic B,
    input logic C,
    input logic X,
    input logic not_A,
    input logic and_B_C,
    input logic b0,
    input logic clk_in_1
);

property SyncIneotid; @(negedge clk_in_1) (A) |-> (not_A) ; endproperty
assert property (SyncIneotid);

property ValidIneotid; @(negedge clk_in_1) (B) &&  (C) |-> (and_B_C) ; endproperty
assert property (ValidIneotid);

property ValidIneotid_2; @(negedge clk_in_1) (A) &&  (B) &&  (C) |-> (X) == (1'b0) ; endproperty
assert property (ValidIneotid_2);

endmodule