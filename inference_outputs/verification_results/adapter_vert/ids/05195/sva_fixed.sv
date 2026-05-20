module twos_complement_sva (
    input logic a,
    input logic add_one,
    input logic inverted,
    input logic ones_comp,
    input logic twos_comp,
    input logic b1,
    input logic clk_in_13
);

property OneComplementeotid; @(posedge clk_in_13) (a) |-> (ones_comp) == (~a) ;endproperty
assert property (OneComplementeotid);

property Inverseeotid; @(posedge clk_in_13) (a) |-> (inverted) == (ones_comp + 4'b1) ;endproperty
assert property (Inverseeotid);

property TwoComplementeotid; @(posedge clk_in_13) (a) |-> (add_one) == (inverted + 4'b1) &&  (  inverted[3]  ) ;endproperty
assert property (TwoComplementeotid);

property TwoComplementeotid_2; @(posedge clk_in_13) (a) |-> (twos_comp) == (add_one) ;endproperty
assert property (TwoComplementeotid_2);

endmodule