module adder_subtractor_sva (
    input logic A,
    input logic B,
    input logic B_comp,
    input logic SUB,
    input logic SUM,
    input logic b1,
    input logic clk_in_1
);

property AddSynceotid; @(posedge clk_in_1) (SUB) |-> (SUM) == (A + B_comp); endproperty
assert property (AddSynceotid);

property SubSynceotid; @(posedge clk_in_1) (SUB) != 1'b1  |-> (SUM) == (A + B); endproperty
assert property (SubSynceotid);

endmodule