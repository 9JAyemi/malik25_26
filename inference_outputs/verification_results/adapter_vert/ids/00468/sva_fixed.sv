module clock_gate_en_sva (
    input logic clk,
    input logic data_in,
    input logic data_out,
    input logic en,
    input logic b0,
    input logic b1
);

property ClockSynceotid; @(posedge clk) (en) |-> data_out == data_in ; endproperty
assert property (ClockSynceotid);

property ClockGateeotid; @(posedge clk) (en) != 1'b1  |-> data_out == 1'b0; endproperty
assert property (ClockGateeotid);

endmodule