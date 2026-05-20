module adder_16bit_signed_unsigned_sva (
    input logic a,
    input logic b,
    input logic cin,
    input logic cout,
    input logic sum,
    input logic unsigned_sum,
    input logic clk_in_15
);

property AdderSynceotid; @(posedge clk_in_15) (a) |-> (unsigned_sum) ;endproperty
assert property (AdderSynceotid);

property AdderSynceotid_2; @(posedge clk_in_15) (a) &&  (b) &&  (cin) |-> (cout) ;endproperty
assert property (AdderSynceotid_2);

property AdderSynceotid_3; @(posedge clk_in_15) (a) &&  (b) &&  (cin) |-> (sum) ;endproperty
assert property (AdderSynceotid_3);

endmodule