module twos_complement_sva (
    input logic A,
    input logic B,
    input logic OUT,
    input logic sel,
    input logic b1,
    input logic clk_in_14
);

property TwosComplementeotid; @(posedge clk_in_14) (A) |-> (OUT) == (~A + 1) ;endproperty
assert property (TwosComplementeotid);

property ValidDataeotid; @(posedge clk_in_14) (sel) |-> (OUT) == (A) ;endproperty
assert property (ValidDataeotid);

property ValidDataeotid_2; @(posedge clk_in_14) (sel) != 1'b1  |-> (OUT) == (B) ;endproperty
assert property (ValidDataeotid_2);

endmodule