module bw_clk_cclk_inv_96x_sva (
    input logic clkout,
    input logic clkin
);

    // clkout must remain the inverse of clkin on clkin rising edges.
    check_inversion_on_clkin_rise: assert property (
        @(posedge clkin) (clkout === ~clkin)
    );

    // clkout must remain the inverse of clkin on clkout rising edges.
    check_inversion_on_clkout_rise: assert property (
        @(posedge clkout) (clkout === ~clkin)
    );

endmodule