module gtwizard_ultrascale_v1_7_1_bit_synchronizer_sva #(
    parameter INITIALIZE = 5'b00000,
    parameter FREQUENCY  = 512
)(
    input logic clk_in,
    input logic i_in,
    input logic o_out
);

    // At the first sampled clock, output starts from INITIALIZE[4].
    check_initial_output_stage4: assert property (
        @(posedge clk_in) $initstate |-> (o_out == INITIALIZE[4])
    );

    // One clock later, output reflects the initialized sync3 stage.
    check_initial_output_stage3: assert property (
        @(posedge clk_in) $initstate |-> ##1 (o_out == INITIALIZE[3])
    );

    // Two clocks later, output reflects the initialized sync2 stage.
    check_initial_output_stage2: assert property (
        @(posedge clk_in) $initstate |-> ##2 (o_out == INITIALIZE[2])
    );

    // Three clocks later, output reflects the initialized sync1 stage.
    check_initial_output_stage1: assert property (
        @(posedge clk_in) $initstate |-> ##3 (o_out == INITIALIZE[1])
    );

    // Four clocks later, output reflects the initialized meta stage.
    check_initial_output_stage0: assert property (
        @(posedge clk_in) $initstate |-> ##4 (o_out == INITIALIZE[0])
    );

    // A sampled 1 on the input appears at the output five clocks later.
    check_sampled_one_reaches_output_in_5_cycles: assert property (
        @(posedge clk_in) (i_in == 1'b1) |-> ##5 (o_out == 1'b1)
    );

    // A sampled 0 on the input appears at the output five clocks later.
    check_sampled_zero_reaches_output_in_5_cycles: assert property (
        @(posedge clk_in) (i_in == 1'b0) |-> ##5 (o_out == 1'b0)
    );

    // After the pipeline fills, output matches the input from five clocks earlier.
    check_output_matches_5cycle_delayed_input: assert property (
        @(posedge clk_in)
        !($initstate || $past($initstate,1) || $past($initstate,2) || $past($initstate,3) || $past($initstate,4))
        |-> (o_out == $past(i_in,5))
    );

    // A sampled rising edge on the input causes a rising edge on the output five clocks later.
    check_input_rise_propagates_to_output_rise: assert property (
        @(posedge clk_in) (!$initstate && $rose(i_in)) |-> ##5 $rose(o_out)
    );

    // A sampled falling edge on the input causes a falling edge on the output five clocks later.
    check_input_fall_propagates_to_output_fall: assert property (
        @(posedge clk_in) (!$initstate && $fell(i_in)) |-> ##5 $fell(o_out)
    );

endmodule