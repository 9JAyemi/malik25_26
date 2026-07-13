module and4_pwr_good_sva (
    input logic X,
    input logic pwrgood_pp0_out_X,
    input logic A_N,
    input logic B,
    input logic C,
    input logic D,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB
);

    // X is the inverted A_N ANDed with B, C, and D.
    check_x_matches_inverted_and: assert property (
        @($global_clock) X == (~A_N & B & C & D)
    );

    // pwrgood_pp0_out_X is X gated by VPWR and VGND.
    check_pwrgood_matches_x_and_power: assert property (
        @($global_clock) pwrgood_pp0_out_X == (X & VPWR & VGND)
    );

    // X must be low when A_N is high.
    check_x_low_when_a_n_high: assert property (
        @($global_clock) A_N |-> !X
    );

    // X must be low when any of B, C, or D is low.
    check_x_low_when_any_input_low: assert property (
        @($global_clock) (!B || !C || !D) |-> !X
    );

    // X must be high when A_N is low and all other inputs are high.
    check_x_high_when_all_inputs_active: assert property (
        @($global_clock) (!A_N && B && C && D) |-> X
    );

    // pwrgood_pp0_out_X must be low when VPWR is low.
    check_pwrgood_low_when_vpwr_low: assert property (
        @($global_clock) !VPWR |-> !pwrgood_pp0_out_X
    );

    // pwrgood_pp0_out_X must be low when VGND is low.
    check_pwrgood_low_when_vgnd_low: assert property (
        @($global_clock) !VGND |-> !pwrgood_pp0_out_X
    );

    // pwrgood_pp0_out_X must be high when X is high and power is good.
    check_pwrgood_high_when_x_and_power_good: assert property (
        @($global_clock) (X && VPWR && VGND) |-> pwrgood_pp0_out_X
    );

    // pwrgood_pp0_out_X must be low when X is low.
    check_pwrgood_low_when_x_low: assert property (
        @($global_clock) !X |-> !pwrgood_pp0_out_X
    );

    // pwrgood_pp0_out_X must be low when any power pin is low.
    check_pwrgood_low_when_any_power_pin_low: assert property (
        @($global_clock) (!VPWR || !VGND) |-> !pwrgood_pp0_out_X
    );

endmodule