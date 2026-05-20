module adder_subtractor_4bit_sva (
    input logic A,
    input logic B,
    input logic SUB,
    input logic result,
    input logic clk_in_1
);

property SubSynceotid; @(posedge clk_in_1) (SUB) |-> result == (A - B) && (  (result[3] == 1) ? 1 : 0 ) ;endproperty
assert property (SubSynceotid);

property AddSynceotid; @(posedge clk_in_1) (SUB) != 1  |-> result == (A + B) && (  (result[3] == 1) ? 1 : 0 ) ;endproperty
assert property (AddSynceotid);

endmodule