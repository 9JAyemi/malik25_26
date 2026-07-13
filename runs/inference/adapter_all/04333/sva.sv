module bw_clk_gclk_inv_r90_192x_sva (
    input logic clkout,
    input logic clkin
);
    // clkout is always the bitwise inversion of clkin.
    check_inversion: assert property (
        @(posedge clkin) clkout == ~clkin
    );

    // If clkin is 0, clkout must be 1.
    check_map_0_to_1: assert property (
        @(posedge clkin) (clkin == 1'b0) |-> (clkout == 1'b1)
    );

    // If clkin is 1, clkout must be 0.
    check_map_1_to_0: assert property (
        @(posedge clkin) (clkin == 1'b1) |-> (clkout == 1'b0)
    );

    // clkout can never equal clkin.
    check_never_equal: assert property (
        @(posedge clkin) clkout != clkin
    );

    // clkout is never X/Z when clkin is known (0/1).
    check_known_when_clkin_known: assert property (
        @(posedge clkin) !$isunknown(clkin) |-> !$isunknown(clkout)
    );

    // clkout and clkin are never both 0 at the same sampled edge.
    check_no_both_zero: assert property (
        @(posedge clkin) !(clkout == 1'b0 && clkin == 1'b0)
    );

    // clkout and clkin are never both 1 at the same sampled edge.
    check_no_both_one: assert property (
        @(posedge clkin) !(clkout == 1'b1 && clkin == 1'b1)
    );

    // clkout is stable across sampled edges when clkin is stable.
    check_stable_when_clkin_stable: assert property (
        @(posedge clkin) $stable(clkin) |-> $stable(clkout)
    );

    // clkout toggles on every sampled edge of clkin.
    check_toggle_each_edge: assert property (
        @(posedge clkin) $changed(clkout)
    );
endmodule