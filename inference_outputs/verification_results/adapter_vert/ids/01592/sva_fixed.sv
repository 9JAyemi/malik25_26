module full_adder_sva (
    input logic A,
    input logic B,
    input logic CI,
    input logic COUT,
    input logic SUM,
    input logic b1,
    input logic clk_in_14
);

property AdderSynceotid; @(posedge clk_in_14) (A) |-> (SUM) == (A ^ B ^ CI); endproperty
assert property (AdderSynceotid);

property CarrySynceotid; @(posedge clk_in_14) (A) &&  (B) &&  (CI) |-> (COUT) == 1'b1 ; endproperty
assert property (CarrySynceotid);

property CarrySynceotid_2; @(posedge clk_in_14) (A) &&  (B) &&  (!CI) ||  (A) &&  (!B) &&  (CI) ||  (!A) &&  (B) &&  (CI)  |-> (COUT) == 1'b1 ; endproperty
assert property (CarrySynceotid_2);

property AdderSynceotid_2; @(posedge clk_in_14) (B) |-> (SUM) == (A ^ B ^ CI); endproperty
assert property (AdderSynceotid_2);

property CarrySynceotid_3; @(posedge clk_in_14) (B) &&  (CI) |-> (COUT) == 1'b1 ; endproperty
assert property (CarrySynceotid_3);

property CarrySynceotid_4; @(posedge clk_in_14) (B) &&  (A) &&  (!CI) ||  (B) &&  (!A) &&  (CI)  |-> (COUT) == 1'b1 ; endproperty
assert property (CarrySynceotid_4);

endmodule