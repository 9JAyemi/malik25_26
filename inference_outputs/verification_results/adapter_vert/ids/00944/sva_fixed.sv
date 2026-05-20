module mux4_1_sva (
    input logic A0,
    input logic A1,
    input logic S,
    input logic X,
    input logic bx,
    input logic clk_in_1
);

property ClockSynceotid; @(posedge clk_in_1) (S) == (0) |-> (X) == (A0) ; endproperty
assert property (ClockSynceotid);

property SyncCheckeotid; @(posedge clk_in_1) (S) == (1) |-> (X) == (A1) ; endproperty
assert property (SyncCheckeotid);

property SyncCheckeotid_2; @(posedge clk_in_1) (S) != 0 && @(posedge clk_in_1) (S) != 1 |-> (X) == 1'bx ; endproperty
assert property (SyncCheckeotid_2);

endmodule