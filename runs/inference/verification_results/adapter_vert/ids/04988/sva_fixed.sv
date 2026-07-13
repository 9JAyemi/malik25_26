module calculator_sva (
    input logic A,
    input logic B,
    input logic add,
    input logic div,
    input logic mul,
    input logic sub,
    input logic b0000000,
    input logic clk_in_1
);

property AddSynceotid; @(posedge clk_in_1) (A) |-> (add) == (A + B) ;endproperty
assert property (AddSynceotid);

property SubSynceotid; @(posedge clk_in_1) (A) |-> (sub) == (A - B) ;endproperty
assert property (SubSynceotid);

property MultSynceotid; @(posedge clk_in_1) (A) |-> (mul) == (A * B) ;endproperty
assert property (MultSynceotid);

property DivSynceotid; @(posedge clk_in_1) (A) &&  (  (B) != 7'b0000000  ) |-> (div) == (A / B) ;endproperty
assert property (DivSynceotid);

endmodule