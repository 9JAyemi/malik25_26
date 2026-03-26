module sky130_fd_sc_hs__tapvgnd2_sva (
    input logic VPWR,
    input logic VGND,
    input logic tap,
    input logic tap_bar
);

    // No explicit clock or reset; sample this combinational cell on the formal global clock.

    // tap follows VGND when the supplies are known and complementary.
    check_tap_matches_vgnd_with_complementary_supplies: assert property (
        @($global_clock) disable iff (1'b0)
        (((VPWR === 1'b1) && (VGND === 1'b0)) ||
         ((VPWR === 1'b0) && (VGND === 1'b1)))
        |-> (tap === VGND)
    );

    // tap_bar follows VPWR when the supplies are known and complementary.
    check_tap_bar_matches_vpwr_with_complementary_supplies: assert property (
        @($global_clock) disable iff (1'b0)
        (((VPWR === 1'b1) && (VGND === 1'b0)) ||
         ((VPWR === 1'b0) && (VGND === 1'b1)))
        |-> (tap_bar === VPWR)
    );

    // tap and tap_bar are complements when the supplies are known and complementary.
    check_outputs_are_complements_with_complementary_supplies: assert property (
        @($global_clock) disable iff (1'b0)
        (((VPWR === 1'b1) && (VGND === 1'b0)) ||
         ((VPWR === 1'b0) && (VGND === 1'b1)))
        |-> (tap_bar === ~tap)
    );

    // With VPWR high and VGND low, tap must be low.
    check_tap_low_when_vpwr_high_and_vgnd_low: assert property (
        @($global_clock) disable iff (1'b0)
        ((VPWR === 1'b1) && (VGND === 1'b0))
        |-> (tap === 1'b0)
    );

    // With VPWR high and VGND low, tap_bar must be high.
    check_tap_bar_high_when_vpwr_high_and_vgnd_low: assert property (
        @($global_clock) disable iff (1'b0)
        ((VPWR === 1'b1) && (VGND === 1'b0))
        |-> (tap_bar === 1'b1)
    );

    // With VPWR low and VGND high, tap must be high.
    check_tap_high_when_vpwr_low_and_vgnd_high: assert property (
        @($global_clock) disable iff (1'b0)
        ((VPWR === 1'b0) && (VGND === 1'b1))
        |-> (tap === 1'b1)
    );

    // With VPWR low and VGND high, tap_bar must be low.
    check_tap_bar_low_when_vpwr_low_and_vgnd_high: assert property (
        @($global_clock) disable iff (1'b0)
        ((VPWR === 1'b0) && (VGND === 1'b1))
        |-> (tap_bar === 1'b0)
    );

endmodule