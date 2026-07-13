module four_bit_adder_sva (
    input logic a,
    input logic b,
    input logic cin,
    input logic cout,
    input logic sum,
    input logic temp_cout,
    input logic temp_sum,
    input logic bxxxxx,
    input logic clk_in_1
);

property AdderSynceotid; @(posedge clk_in_1) (a) |-> (temp_sum) ;endproperty
assert property (AdderSynceotid);

property AdderSynceotid_2; @(posedge clk_in_1) (a) &&  (b) &&  (cin) |-> (sum) == (temp_sum) ;endproperty
assert property (AdderSynceotid_2);

property AdderSynceotid_3; @(posedge clk_in_1) (a) &&  (b) &&  (cin) |-> (cout) == (temp_cout) ;endproperty
assert property (AdderSynceotid_3);

property AdderSynceotid_4; @(posedge clk_in_1) (a) &&  (b) &&  (cin) &&  (  (temp_sum)  != 5'bxxxxx  ) |-> (temp_cout) ;endproperty
assert property (AdderSynceotid_4);

endmodule