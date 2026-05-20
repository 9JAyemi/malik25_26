module freq_divider_sva (
    input logic clk_in,
    input logic clk_out,
    input logic count,
    input logic n
);

property ClockSynceotid; @(posedge clk_in) (count) == (n - 1) |-> clk_out == ~clk_out ;endproperty
assert property (ClockSynceotid);

property ClockSynceotid_2; @(posedge clk_in) (count) != (n - 1) |-> clk_out == clk_out ;endproperty
assert property (ClockSynceotid_2);

endmodule