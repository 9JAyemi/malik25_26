module carry_lookahead_adder_sva (
    input logic a,
    input logic b,
    input logic cout,
    input logic sum,
    input logic a_15,
    input logic a_4,
    input logic b0,
    input logic b_15,
    input logic c_0,
    input logic c_1,
    input logic c_2,
    input logic c_3,
    input logic clk_in_1
);

property CarrySynceotid; @(posedge clk_in_1) (a) |-> (a_15) ;endproperty
assert property (CarrySynceotid);

property CarrySynceotid_2; @(posedge clk_in_1) (b) |-> (b_15) ;endproperty
assert property (CarrySynceotid_2);

property SyncAddereotid; @(posedge clk_in_1) (a) &&  (b) &&  ( 1'b0 ) |-> (sum) == (  {c_3, c_2, c_1, c_0, a_15: a_4} ) ;endproperty
assert property (SyncAddereotid);

property SyncCarryeotid; @(posedge clk_in_1) (a) &&  (b) &&  ( 1'b0 ) |-> (cout) == (  c_3 ) ;endproperty
assert property (SyncCarryeotid);

endmodule