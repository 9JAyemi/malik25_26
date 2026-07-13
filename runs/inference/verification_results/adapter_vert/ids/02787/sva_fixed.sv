module twos_complement_sva (
    input logic add_one,
    input logic binary,
    input logic invert,
    input logic twos_comp,
    input logic clk_in_1
);

property InvertOnClockRiseeotid; @(posedge clk_in_1) (binary) |-> (invert) ;endproperty
assert property (InvertOnClockRiseeotid);

property AddOneeotid; @(posedge clk_in_1) (invert) |-> (add_one) ;endproperty
assert property (AddOneeotid);

property TwoCompeotid; @(posedge clk_in_1) (add_one) |-> (twos_comp) ;endproperty
assert property (TwoCompeotid);

endmodule