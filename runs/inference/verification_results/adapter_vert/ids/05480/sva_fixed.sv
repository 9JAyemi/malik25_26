module adder_sva (
    input logic A,
    input logic B,
    input logic C,
    input logic CO,
    input logic sum,
    input logic b0000000,
    input logic b1,
    input logic clk_in_1
);

property AdderSynceotid; @(posedge clk_in_1) (A) |-> (C) == (sum); endproperty
assert property (AdderSynceotid);

property AdderSynceotid_2; @(posedge clk_in_1) (A) &&  (B) |-> (CO) == (1'b1); endproperty
assert property (AdderSynceotid_2);

property SyncAddereotid; @(posedge clk_in_1) (A) &&  (B) ||  (A) &&  (!B) ||  (!A) &&  (B)  |-> (C) != 7'b0000000 ; endproperty
assert property (SyncAddereotid);

endmodule