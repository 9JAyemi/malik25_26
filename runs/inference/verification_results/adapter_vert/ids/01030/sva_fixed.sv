module constant_generator_sva (
    input logic ce,
    input logic clk,
    input logic clr,
    input logic op_reg,
    input logic b0,
    input logic b1
);

property ResetSynceotid; @(posedge clk) (clr) |-> op_reg == 1'b0 ;endproperty
assert property (ResetSynceotid);

property ClockSynceotid; @(posedge clk) (clr) != 1'b1 &&  (ce)  |-> op_reg == 1'b1 ;endproperty
assert property (ClockSynceotid);

endmodule