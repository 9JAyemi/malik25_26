module adder_sva (
    input logic A,
    input logic B,
    input logic sum,
    input logic b0,
    input logic clk_in_1
);

property AddOneeotid; @(posedge clk_in_1) (A) |-> (sum) == ( {1'b0, A} + {1'b0, B} );endproperty
assert property (AddOneeotid);

endmodule