module SimpleCalculator_sva (
    input logic a,
    input logic b,
    input logic op,
    input logic result,
    input logic clk_in_1
);

property AddSynceotid; @(posedge clk_in_1) (op) == (0) |-> (result) == (a + b) ; endproperty
assert property (AddSynceotid);

property SubSynceotid; @(posedge clk_in_1) (op) != 0  |-> (result) == (a - b) ; endproperty
assert property (SubSynceotid);

endmodule