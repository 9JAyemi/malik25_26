module calculator_sva (
    input logic A,
    input logic B,
    input logic op,
    input logic result,
    input logic b00,
    input logic b01,
    input logic b10,
    input logic b11,
    input logic clk_in_1
);

property AddSynceotid; @(posedge clk_in_1) (op) == (2'b00) |-> (result) == (A + B) ; endproperty
assert property (AddSynceotid);

property SubSynceotid; @(posedge clk_in_1) (op) == (2'b01) |-> (result) == (A - B) ; endproperty
assert property (SubSynceotid);

property MultSynceotid; @(posedge clk_in_1) (op) == (2'b10) |-> (result) == (A * B) ; endproperty
assert property (MultSynceotid);

property DivSynceotid; @(posedge clk_in_1) (op) == (2'b11) |-> (result) == (A / B) ; endproperty
assert property (DivSynceotid);

endmodule