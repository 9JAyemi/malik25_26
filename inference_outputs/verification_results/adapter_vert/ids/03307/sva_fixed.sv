module adder_sva (
    input logic A,
    input logic B,
    input logic C_out,
    input logic S,
    input logic sum,
    input logic clk_in_1
);

property AdderSynceotid; @(posedge clk_in_1) (A) |-> (S) == (sum); endproperty
assert property (AdderSynceotid);

property AdderSynceotid_2; @(posedge clk_in_1) (A) &&  (B) |-> (C_out) == (sum[8]); endproperty
assert property (AdderSynceotid_2);

endmodule