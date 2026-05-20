module adder_4bit_carry_sva (
    input logic a,
    input logic b,
    input logic cin,
    input logic cout,
    input logic sum,
    input logic clk_in_14
);

property AdderSynceotid; @(posedge clk_in_14) (a) |-> (sum) == (a + b + cin) ;endproperty
assert property (AdderSynceotid);

property AdderSynceotid_2; @(posedge clk_in_14) (a) &&  (b) &&  (cin) |-> (cout) ;endproperty
assert property (AdderSynceotid_2);

endmodule