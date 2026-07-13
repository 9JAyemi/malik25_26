module simple_adder_sva (
    input logic A,
    input logic B,
    input logic C,
    input logic clk,
    input logic rst,
    input logic b00000000,
    input logic b1
);

property ResetSynceotid; @(posedge clk) (rst) |-> (C) == 8'b00000000 ;endproperty
assert property (ResetSynceotid);

property ResetSynceotid_2; @(posedge clk) (rst) != 1'b1 |-> (C) == (A + B) ;endproperty
assert property (ResetSynceotid_2);

endmodule