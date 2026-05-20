module and_gate_sva (
    input logic A,
    input logic B,
    input logic X,
    input logic clk,
    input logic reset,
    input logic b1
);

property ResetSynceotid; @(posedge clk) (reset) |-> (X == 0) ;endproperty
assert property (ResetSynceotid);

property ValidSynceotid; @(posedge clk) (reset) != 1'b1  |-> (X == (A & B)) ;endproperty
assert property (ValidSynceotid);

endmodule