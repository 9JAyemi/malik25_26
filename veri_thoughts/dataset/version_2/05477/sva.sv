module var12_multi_sva (
    input logic clk,
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
    input logic L,
    input logic valid
);

    wire [7:0] min_value;
    wire [7:0] max_weight;
    wire [7:0] max_volume;
    wire [7:0] total_value;
    wire [7:0] total_weight;
    wire [7:0] total_volume;

    assign min_value = 8'd107;
    assign max_weight = 8'd60;
    assign max_volume = 8'd60;

    assign total_value =
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
          + K * 8'd30
          + L * 8'd8;

    assign total_weight =
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
          + K * 8'd5
          + L * 8'd13;

    assign total_volume =
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
          + K * 8'd5
          + L * 8'd2;

    // valid must match the RTL threshold expression.
    check_valid_definition: assert property (
        @(posedge clk)
        valid == ((total_value >= min_value) && (total_weight <= max_weight) && (total_volume <= max_volume))
    );

    // A valid result must meet the minimum value threshold.
    check_valid_requires_min_value: assert property (
        @(posedge clk)
        valid |-> (total_value >= min_value)
    );

    // A valid result must stay within the weight limit.
    check_valid_requires_weight_limit: assert property (
        @(posedge clk)
        valid |-> (total_weight <= max_weight)
    );

    // A valid result must stay within the volume limit.
    check_valid_requires_volume_limit: assert property (
        @(posedge clk)
        valid |-> (total_volume <= max_volume)
    );

    // An invalid result must violate at least one threshold.
    check_invalid_has_failing_constraint: assert property (
        @(posedge clk)
        (!valid) |-> ((total_value < min_value) || (total_weight > max_weight) || (total_volume > max_volume))
    );

    // Too little value must force valid low.
    check_low_value_forces_valid_low: assert property (
        @(posedge clk)
        (total_value < min_value) |-> (!valid)
    );

    // Too much weight must force valid low.
    check_overweight_forces_valid_low: assert property (
        @(posedge clk)
        (total_weight > max_weight) |-> (!valid)
    );

    // Too much volume must force valid low.
    check_overvolume_forces_valid_low: assert property (
        @(posedge clk)
        (total_volume > max_volume) |-> (!valid)
    );

    // Selecting no items must produce an invalid result.
    check_empty_selection_invalid: assert property (
        @(posedge clk)
        (!A && !B && !C && !D && !E && !F && !G && !H && !I && !J && !K && !L) |-> (!valid)
    );

    // A known threshold-meeting selection must produce a valid result.
    check_known_feasible_selection_valid: assert property (
        @(posedge clk)
        (!A && !B && !C && D && E && !F && G && H && !I && J && K && !L) |-> valid
    );

endmodule