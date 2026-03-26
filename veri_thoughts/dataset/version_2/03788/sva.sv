module var11_multi_sva (
    input logic A,
    input logic B,
    input logic C,
    input logic D,
    input logic E,
    input logic F,
    input logic G,
    input logic H,
    input logic I,
    input logic J,
    input logic K,
    input logic valid
);

    wire [7:0] min_value  = 8'd107;
    wire [7:0] max_weight = 8'd60;
    wire [7:0] max_volume = 8'd60;

    wire [7:0] total_value =
          A * 8'd4
        + B * 8'd8
        + C * 8'd0
        + D * 8'd20
        + E * 8'd10
        + F * 8'd12
        + G * 8'd18
        + H * 8'd14
        + I * 8'd6
        + J * 8'd15
        + K * 8'd30;

    wire [7:0] total_weight =
          A * 8'd28
        + B * 8'd8
        + C * 8'd27
        + D * 8'd18
        + E * 8'd27
        + F * 8'd28
        + G * 8'd6
        + H * 8'd1
        + I * 8'd20
        + J * 8'd0
        + K * 8'd5;

    wire [7:0] total_volume =
          A * 8'd27
        + B * 8'd27
        + C * 8'd4
        + D * 8'd4
        + E * 8'd0
        + F * 8'd24
        + G * 8'd4
        + H * 8'd20
        + I * 8'd12
        + J * 8'd15
        + K * 8'd5;

    // valid must match the implemented threshold comparison.
    check_valid_definition: assert property (
        @($global_clock)
        valid == ((total_value >= min_value) &&
                  (total_weight <= max_weight) &&
                  (total_volume <= max_volume))
    );

    // Value below the minimum must force valid low.
    check_invalid_if_value_below_min: assert property (
        @($global_clock)
        (total_value < min_value) |-> !valid
    );

    // Weight above the maximum must force valid low.
    check_invalid_if_weight_above_max: assert property (
        @($global_clock)
        (total_weight > max_weight) |-> !valid
    );

    // Volume above the maximum must force valid low.
    check_invalid_if_volume_above_max: assert property (
        @($global_clock)
        (total_volume > max_volume) |-> !valid
    );

    // Meeting all three constraints must make valid high.
    check_valid_if_all_constraints_met: assert property (
        @($global_clock)
        ((total_value >= min_value) &&
         (total_weight <= max_weight) &&
         (total_volume <= max_volume)) |-> valid
    );

    // Selecting no items must be invalid.
    check_empty_selection_invalid: assert property (
        @($global_clock)
        (!A && !B && !C && !D && !E && !F && !G && !H && !I && !J && !K) |-> !valid
    );

    // This bundle is under the value threshold while staying within limits.
    check_low_value_bundle_invalid: assert property (
        @($global_clock)
        (!A && !B && !C && D && !E && !F && G && H && !I && J && K) |-> !valid
    );

    // This bundle exactly reaches the minimum value within both limits.
    check_threshold_bundle_valid: assert property (
        @($global_clock)
        (!A && !B && !C && D && E && !F && G && H && !I && J && K) |-> valid
    );

    // This bundle exceeds weight while volume remains within the limit.
    check_overweight_bundle_invalid: assert property (
        @($global_clock)
        (!A && !B && !C && D && E && !F && G && H && I && J && K) |-> !valid
    );

    // This bundle exceeds volume while weight remains within the limit.
    check_overvolume_bundle_invalid: assert property (
        @($global_clock)
        (!A && B && !C && D && !E && !F && G && H && I && J && K) |-> !valid
    );

endmodule