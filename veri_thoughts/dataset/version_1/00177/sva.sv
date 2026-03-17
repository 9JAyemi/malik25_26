module var15_multi_sva (
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
    input logic M,
    input logic N,
    input logic O,
    input logic valid
);

    wire [7:0] min_value = 8'd120;
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
        + K * 8'd30
        + L * 8'd8
        + M * 8'd16
        + N * 8'd18
        + O * 8'd18;

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
        + K * 8'd5
        + L * 8'd13
        + M * 8'd8
        + N * 8'd14
        + O * 8'd22;

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
        + K * 8'd5
        + L * 8'd2
        + M * 8'd9
        + N * 8'd28
        + O * 8'd19;

    // valid must match the three threshold comparisons.
    check_valid_definition: assert property (
        @(posedge clk)
        valid == ((total_value >= min_value) && (total_weight <= max_weight) && (total_volume <= max_volume))
    );

    // A valid result must meet the minimum value threshold.
    check_valid_implies_min_value: assert property (
        @(posedge clk)
        valid |-> (total_value >= min_value)
    );

    // A valid result must not exceed the weight limit.
    check_valid_implies_max_weight: assert property (
        @(posedge clk)
        valid |-> (total_weight <= max_weight)
    );

    // A valid result must not exceed the volume limit.
    check_valid_implies_max_volume: assert property (
        @(posedge clk)
        valid |-> (total_volume <= max_volume)
    );

    // Meeting all thresholds must assert valid.
    check_thresholds_imply_valid: assert property (
        @(posedge clk)
        ((total_value >= min_value) && (total_weight <= max_weight) && (total_volume <= max_volume)) |-> valid
    );

    // Falling below the minimum value must deassert valid.
    check_low_value_blocks_valid: assert property (
        @(posedge clk)
        (total_value < min_value) |-> !valid
    );

    // Exceeding the weight limit must deassert valid.
    check_high_weight_blocks_valid: assert property (
        @(posedge clk)
        (total_weight > max_weight) |-> !valid
    );

    // Exceeding the volume limit must deassert valid.
    check_high_volume_blocks_valid: assert property (
        @(posedge clk)
        (total_volume > max_volume) |-> !valid
    );

endmodule