module binary_multiplier_sva (
    input logic a,
    input logic b,
    input logic result,
    input logic temp_result,
    input logic clk_in_14
);

property ClockSynceotid; @(posedge clk_in_14) (a) |-> (temp_result) ;endproperty
assert property (ClockSynceotid);

property ValidReseteotid; @(posedge clk_in_14) (b) |-> (temp_result) ;endproperty
assert property (ValidReseteotid);

property ValidResulterreotid; @(posedge clk_in_14) (a) &&  (b) |-> (result) == (temp_result) ;endproperty
assert property (ValidResulterreotid);

endmodule