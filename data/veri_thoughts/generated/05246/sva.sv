module max_min_value_sva (
    input logic signed [15:0] num_in1,
    input logic signed [15:0] num_in2,
    input logic max_or_min,
    input logic reset,
    input logic [15:0] num_out,
    input logic clk,
    input logic [15:0] max_value,
    input logic [15:0] min_value,
    input logic [1:0] stage
);

    // Reset clears stage and output.
    check_reset_clears_state: assert property (
        @(posedge clk) reset |=> (stage == 2'd0 && num_out == 16'd0)
    );

    // num_in1 greater makes num_in1 the max and num_in2 the min.
    check_max_min_map_in1_gt_in2: assert property (
        @(posedge clk) disable iff (reset)
        (num_in1 > num_in2) |-> (max_value == num_in1 && min_value == num_in2)
    );

    // num_in1 not greater makes num_in2 the max and num_in1 the min.
    check_max_min_map_in1_le_in2: assert property (
        @(posedge clk) disable iff (reset)
        (num_in1 <= num_in2) |-> (max_value == num_in2 && min_value == num_in1)
    );

    // Stage 0 advances to stage 1 on the next cycle.
    check_stage_0_to_1: assert property (
        @(posedge clk) disable iff (reset)
        (stage == 2'd0) |=> (stage == 2'd1)
    );

    // Stage 1 advances back to stage 0 on the next cycle.
    check_stage_1_to_0: assert property (
        @(posedge clk) disable iff (reset)
        (stage == 2'd1) |=> (stage == 2'd0)
    );

    // Stage 0 with max selected loads max_value into the output.
    check_stage_0_loads_max_value: assert property (
        @(posedge clk) disable iff (reset)
        (stage == 2'd0 && max_or_min) |=> (num_out == $past(max_value))
    );

    // Stage 0 with min selected loads min_value into the output.
    check_stage_0_loads_min_value: assert property (
        @(posedge clk) disable iff (reset)
        (stage == 2'd0 && !max_or_min) |=> (num_out == $past(min_value))
    );

    // Stage 1 holds the output value.
    check_stage_1_holds_output: assert property (
        @(posedge clk) disable iff (reset)
        (stage == 2'd1) |=> (num_out == $past(num_out))
    );

endmodule