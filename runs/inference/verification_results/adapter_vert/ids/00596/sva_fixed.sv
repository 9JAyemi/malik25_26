module inverter_sva (
    input logic ce,
    input logic clk,
    input logic clr,
    input logic ip,
    input logic op,
    input logic op_reg,
    input logic b0
);

property ClockSynceotid; @(posedge clk) (ce) |-> op_reg == ~ip ;endproperty
assert property (ClockSynceotid);

property ResetSynceotid; @(posedge clk) (clr) |-> op == 1'b0 ;endproperty
assert property (ResetSynceotid);

endmodule