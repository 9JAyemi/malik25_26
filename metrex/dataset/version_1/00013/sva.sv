module bw_clk_cclk_inv_128x_sva (
    input logic clkout,
    input logic clkin
);
    // Analysis summary:
    // - Clocks: No dedicated clock in RTL; assertions sample on edges of clkin and clkout.
    // - Reset: None present in RTL.
    // - Logic type: Purely combinational (clkout is the inversion of clkin).
    // - Behavior: clkout = ~clkin at all times.

    // Inversion must hold when sampled on the rising edge of clkin.
    check_inversion_on_clkin_posedge: assert property (
        @(posedge clkin) clkout == ~clkin
    );

    // Inversion must hold when sampled on the falling edge of clkin.
    check_inversion_on_clkin_negedge: assert property (
        @(negedge clkin) clkout == ~clkin
    );

    // Inversion must hold when sampled on the rising edge of clkout.
    check_inversion_on_clkout_posedge: assert property (
        @(posedge clkout) clkin == ~clkout
    );

    // Inversion must hold when sampled on the falling edge of clkout.
    check_inversion_on_clkout_negedge: assert property (
        @(negedge clkout) clkin == ~clkout
    );

    // Input and output must be complementary when sampled on clkin posedges.
    check_complement_on_clkin_posedge: assert property (
        @(posedge clkin) clkin != clkout
    );

    // Input and output must be complementary when sampled on clkout posedges.
    check_complement_on_clkout_posedge: assert property (
        @(posedge clkout) clkin != clkout
    );

endmodule