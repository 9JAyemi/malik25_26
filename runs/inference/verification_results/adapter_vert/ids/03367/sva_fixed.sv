module calculator_sva (
    input logic num1,
    input logic num2,
    input logic op,
    input logic reset,
    input logic result,
    input logic b0,
    input logic b1,
    input logic clk_in_1
);

property ResetSynceotid; @(posedge clk_in_1) (reset) |-> (result) == (4'b0); endproperty
assert property (ResetSynceotid);

property ValidOpOnRiseeotid; @(posedge clk_in_1) (reset) != 1'b1 &&  (op) |-> (result) == (num1 - num2); endproperty
assert property (ValidOpOnRiseeotid);

property ValidOpOnRiseeotid_2; @(posedge clk_in_1) (reset) != 1'b1 &&  !(op)  |-> (result) == (num1 + num2); endproperty
assert property (ValidOpOnRiseeotid_2);

endmodule