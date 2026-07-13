module my_module_sva (
    input logic A1,
    input logic A2,
    input logic A2_A3,
    input logic A3,
    input logic X,
    input logic clk_in_15
);

property ClockSynceotid; @(posedge clk_in_15) (A1) |-> (A2_A3) ;endproperty
assert property (ClockSynceotid);

property ClockSynceotid_2; @(posedge clk_in_15) (A2) &&  ( ! (A3) ) |-> (X) ;endproperty
assert property (ClockSynceotid_2);

endmodule