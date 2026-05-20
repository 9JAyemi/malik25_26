module add_sub_sva (
    input logic A,
    input logic B,
    input logic OUT,
    input logic SUB,
    input logic b1,
    input logic clk_in_1
);

property AddSynceotid; @(posedge clk_in_1) (SUB) |-> (OUT) == (B - A) ; endproperty
assert property (AddSynceotid);

property AddSynceotid_2; @(posedge clk_in_1) (SUB) != 1'b1  |-> (OUT) == (A + B) ; endproperty
assert property (AddSynceotid_2);

endmodule