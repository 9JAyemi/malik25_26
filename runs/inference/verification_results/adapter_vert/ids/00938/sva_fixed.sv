module four_bit_adder_sva (
    input logic A,
    input logic B,
    input logic Cin,
    input logic carry,
    input logic sum,
    input logic clk_in_1
);

property AdderSynceotid; @(posedge clk_in_1) (A) |-> (sum) ; endproperty
assert property (AdderSynceotid);

property AdderSynceotid_2; @(posedge clk_in_1) (A) &&  (B) &&  (Cin) |-> (carry) ; endproperty
assert property (AdderSynceotid_2);

property AdderSynceotid_3; @(posedge clk_in_1) (A) &&  (B) &&  (!Cin) |-> (sum) ; endproperty
assert property (AdderSynceotid_3);

property AdderSynceotid_4; @(posedge clk_in_1) (A) ||  (B) ||  (Cin) |-> (carry) ; endproperty
assert property (AdderSynceotid_4);

property AdderSynceotid_5; @(posedge clk_in_1) (A) &&  (!B) &&  (Cin) |-> (sum) ; endproperty
assert property (AdderSynceotid_5);

property AdderSynceotid_6; @(posedge clk_in_1) (A) &&  (!B) &&  (!Cin) |-> (sum) ; endproperty
assert property (AdderSynceotid_6);

property AdderSynceotid_7; @(posedge clk_in_1) (!A) &&  (B) &&  (Cin) |-> (sum) ; endproperty
assert property (AdderSynceotid_7);

property AdderSynceotid_8; @(posedge clk_in_1) (!A) &&  (B) &&  (!Cin) |-> (sum) ; endproperty
assert property (AdderSynceotid_8);

property AdderSynceotid_9; @(posedge clk_in_1) (!A) &&  (!B) &&  (Cin) |-> (carry) ; endproperty
assert property (AdderSynceotid_9);

property AdderSynceotid_10; @(posedge clk_in_1) (!A) &&  (!B) &&  (!Cin) |-> (sum) ; endproperty
assert property (AdderSynceotid_10);

endmodule