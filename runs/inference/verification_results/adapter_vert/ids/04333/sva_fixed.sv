module bw_clk_gclk_inv_r90_192x_sva (
    input logic clkin,
    input logic clkout,
    input logic clk_osc_19
);

property ClockSynceotid; @(posedge clk_osc_19) ( clkout ) == (  ~( clkin )  ); endproperty
assert property (ClockSynceotid);

endmodule