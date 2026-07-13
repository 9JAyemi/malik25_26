module adder_4bit_sva (
    input logic A,
    input logic B,
    input logic Cin,
    input logic Cout,
    input logic S,
    input logic Sum,
    input logic b0,
    input logic clk_in_16
);

property AdderSynceotid; @(posedge clk_in_16) (A) |-> (Sum) == ({1'b0, A} + {1'b0, B} + Cin); endproperty
assert property (AdderSynceotid);

property AdderSynceotid_2; @(posedge clk_in_16) (A) |-> (S) == (Sum[3:0]); endproperty
assert property (AdderSynceotid_2);

property AdderSynceotid_3; @(posedge clk_in_16) (A) |-> (Cout) == (Sum[4]); endproperty
assert property (AdderSynceotid_3);

endmodule