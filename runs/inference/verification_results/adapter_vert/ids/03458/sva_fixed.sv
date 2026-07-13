module binary_adder_sva (
    input logic a,
    input logic b,
    input logic carry_in,
    input logic carry_out,
    input logic sum,
    input logic b0,
    input logic b1,
    input logic clk_in_1
);

property AddOneeotid; @(posedge clk_in_1) (a) != (b) && (carry_in) |-> (sum) != (a) && (sum) != (b); endproperty
assert property (AddOneeotid);

property CarrySynceotid; @(posedge clk_in_1) (a) != (b) && (carry_in) &&  (  (a) != (b)  && (carry_in) ) |-> (carry_out) == 1'b1 ; endproperty
assert property (CarrySynceotid);

property SyncAddereotid; @(posedge clk_in_1) (a) == (b) && (carry_in) |-> (sum) == 1'b1 ; endproperty
assert property (SyncAddereotid);

property SyncCarryeotid; @(posedge clk_in_1) (a) != (b) && !(carry_in)  |-> (sum) != (a) && (sum) != (b); endproperty
assert property (SyncCarryeotid);

property SyncCarryeotid_2; @(posedge clk_in_1) (a) != (b) && !(carry_in) &&  (  (a) != (b)  && !(carry_in) ) |-> (carry_out) == 1'b0 ; endproperty
assert property (SyncCarryeotid_2);

property SyncCarryeotid_3; @(posedge clk_in_1) (a) == (b) && !(carry_in) |-> (sum) == 1'b0 ; endproperty
assert property (SyncCarryeotid_3);

endmodule