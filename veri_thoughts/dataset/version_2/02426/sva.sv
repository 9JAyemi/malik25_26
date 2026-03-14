module velocityControlHdl_Dynamic_Saturation_sva (
    input  logic signed [17:0] up,
    input  logic signed [35:0] u,
    input  logic signed [17:0] lo,
    input  logic signed [35:0] y,
    input  logic               sat_mode
);
    // Local recomputation of DUT casts (sign-extend and shift-left by 10)
    logic signed [35:0] up_cast;
    logic signed [35:0] lo_cast;
    assign up_cast = { {8{up[17]}}, up, 10'b0 };
    assign lo_cast = { {8{lo[17]}}, lo, 10'b0 };

    ///// Saturation behavior /////
    // When above upper bound, y saturates to up_cast.
    check_upper_violation_saturates_high: assert property (
        @($global_clock) (u > up_cast) |-> (y == up_cast)
    );

    // When below lower bound and not above upper, y saturates to lo_cast.
    check_lower_violation_saturates_low: assert property (
        @($global_clock) (u < lo_cast) && !(u > up_cast) |-> (y == lo_cast)
    );

    // When within [lo_cast, up_cast], y passes through u.
    check_passthrough_in_range: assert property (
        @($global_clock) (u >= lo_cast) && (u <= up_cast) |-> (y == u)
    );

    // If both violations hold (lo_cast > up_cast case), y chooses upper saturation.
    check_both_violations_choose_upper: assert property (
        @($global_clock) (u > up_cast) && (u < lo_cast) |-> (y == up_cast)
    );

    // y is always one of {u, lo_cast, up_cast}.
    check_y_choice_set: assert property (
        @($global_clock) ((y == u) || (y == lo_cast) || (y == up_cast))
    );

    ///// sat_mode definition /////
    // sat_mode reflects out-of-range condition: (u > up_cast) || (u < lo_cast).
    check_sat_mode_definition: assert property (
        @($global_clock) sat_mode == ((u > up_cast) || (u < lo_cast))
    );

    // If u is below lower bound, sat_mode is asserted.
    check_u_below_implies_sat: assert property (
        @($global_clock) (u < lo_cast) |-> sat_mode
    );

    // If u is above upper bound, sat_mode is asserted.
    check_u_above_implies_sat: assert property (
        @($global_clock) (u > up_cast) |-> sat_mode
    );

    // If u is within [lo_cast, up_cast], sat_mode is deasserted.
    check_in_range_implies_no_sat: assert property (
        @($global_clock) (u >= lo_cast) && (u <= up_cast) |-> !sat_mode
    );

    ///// y vs u relationship via sat_mode /////
    // When sat_mode is asserted, y must differ from u.
    check_sat_mode_implies_y_differs: assert property (
        @($global_clock) sat_mode |-> (y != u)
    );

    // When sat_mode is deasserted, y equals u.
    check_no_sat_mode_implies_passthrough: assert property (
        @($global_clock) !sat_mode |-> (y == u)
    );

    ///// Consistency at equality points /////
    // If y equals up_cast, then u is at or above up_cast.
    check_y_eq_up_implies_u_ge_up: assert property (
        @($global_clock) (y == up_cast) |-> (u >= up_cast)
    );

    // If y equals lo_cast, then u is at or below lo_cast.
    check_y_eq_lo_implies_u_le_lo: assert property (
        @($global_clock) (y == lo_cast) |-> (u <= lo_cast)
    );
endmodule