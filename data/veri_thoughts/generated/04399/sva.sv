module bw_clk_gclk_inv_192x_sva (
    input logic clkout,
    input logic clkin
);

    // clkout stays inverted relative to clkin on rising input edges.
    check_clkout_inverts_clkin_on_rise: assert property (
        @(posedge clkin) clkout == ~clkin
    );

    // clkout stays inverted relative to clkin on falling input edges.
    check_clkout_inverts_clkin_on_fall: assert property (
        @(negedge clkin) clkout == ~clkin
    );

endmodule