module ripple_carry_adder_sva (
    input logic A,
    input logic B,
    input logic cin,
    input logic cout,
    input logic sum,
    input logic clk_in_1
);

property AdderSynceotid; @(posedge clk_in_1) (A) |-> (sum) ; endproperty
assert property (AdderSynceotid);

property CarrySynceotid; @(posedge clk_in_1) (A) &&  (B) &&  (cin) |->  (cout) ; endproperty
assert property (CarrySynceotid);

property AdderSynceotid_2; @(posedge clk_in_1) (A) &&  (B) &&  (cin) |->  (sum) ; endproperty
assert property (AdderSynceotid_2);

property AdderSynceotid_3; @(posedge clk_in_1) (A) &&  (B) &&  (cin) &&  (  ! (A)  &&  ! (B)  &&  ! (cin) ) |->  (  ! (sum)  &&  ! (cout) ) ; endproperty
assert property (AdderSynceotid_3);

endmodule