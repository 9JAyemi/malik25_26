module adder_4bit_sva (
    input logic a,
    input logic b,
    input logic cin,
    input logic cout,
    input logic s,
    input logic sum,
    input logic clk_in_1
);

property AdderSynceotid; @(posedge clk_in_1) (a) |-> (sum) == (a + b + cin) ;endproperty
assert property (AdderSynceotid);

property AdderSynceotid_2; @(posedge clk_in_1) (a) &&  (b) &&  (cin) |->  (cout) ==  (sum[4]) ;endproperty
assert property (AdderSynceotid_2);

property SyncAddereotid; @(posedge clk_in_1) (a) &&  (b) &&  (cin) |->  (s) ==  (sum[3:0]) ;endproperty
assert property (SyncAddereotid);

endmodule