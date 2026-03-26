module pipeline_sva (
    input logic clk,
    input logic clk_ena,
    input logic in_stream,
    input logic reset,
    input logic pipeline_reg_0,
    input logic pipeline_reg_1,
    input logic pipeline_reg_2,
    input logic pipeline_reg_3,
    input logic pipeline_reg_4,
    input logic pipeline_reg_5,
    input logic pipeline_reg_6,
    input logic pipeline_reg_7,
    input logic pipeline_reg_8,
    input logic pipeline_reg_9,
    input logic pipeline_reg_10,
    input logic pipeline_reg_11,
    input logic pipeline_reg_12,
    input logic pipeline_reg_13,
    input logic pipeline_reg_14,
    input logic pipeline_reg_15,
    input logic pipeline_reg_16
);

    // Reset clears all pipeline stages.
    check_reset_clears_pipeline: assert property (
        @(posedge clk)
        reset |=> ({pipeline_reg_16, pipeline_reg_15, pipeline_reg_14, pipeline_reg_13,
                    pipeline_reg_12, pipeline_reg_11, pipeline_reg_10, pipeline_reg_9,
                    pipeline_reg_8, pipeline_reg_7, pipeline_reg_6, pipeline_reg_5,
                    pipeline_reg_4, pipeline_reg_3, pipeline_reg_2, pipeline_reg_1,
                    pipeline_reg_0} == 17'b0)
    );

    // The pipeline holds state when clock enable is low.
    check_hold_when_disabled: assert property (
        @(posedge clk) disable iff (reset)
        !clk_ena |=> $stable({pipeline_reg_16, pipeline_reg_15, pipeline_reg_14, pipeline_reg_13,
                              pipeline_reg_12, pipeline_reg_11, pipeline_reg_10, pipeline_reg_9,
                              pipeline_reg_8, pipeline_reg_7, pipeline_reg_6, pipeline_reg_5,
                              pipeline_reg_4, pipeline_reg_3, pipeline_reg_2, pipeline_reg_1,
                              pipeline_reg_0})
    );

    // Stage 0 captures the input when enabled.
    check_stage0_captures_input: assert property (
        @(posedge clk) disable iff (reset)
        clk_ena |=> (pipeline_reg_0 == $past(in_stream))
    );

    // Stage 1 captures stage 0 when enabled.
    check_stage1_captures_stage0: assert property (
        @(posedge clk) disable iff (reset)
        clk_ena |=> (pipeline_reg_1 == $past(pipeline_reg_0))
    );

    // Stage 2 captures stage 1 when enabled.
    check_stage2_captures_stage1: assert property (
        @(posedge clk) disable iff (reset)
        clk_ena |=> (pipeline_reg_2 == $past(pipeline_reg_1))
    );

    // Stage 3 captures stage 2 when enabled.
    check_stage3_captures_stage2: assert property (
        @(posedge clk) disable iff (reset)
        clk_ena |=> (pipeline_reg_3 == $past(pipeline_reg_2))
    );

    // Stage 4 captures stage 3 when enabled.
    check_stage4_captures_stage3: assert property (
        @(posedge clk) disable iff (reset)
        clk_ena |=> (pipeline_reg_4 == $past(pipeline_reg_3))
    );

    // Stage 5 captures stage 4 when enabled.
    check_stage5_captures_stage4: assert property (
        @(posedge clk) disable iff (reset)
        clk_ena |=> (pipeline_reg_5 == $past(pipeline_reg_4))
    );

    // Stage 6 captures stage 5 when enabled.
    check_stage6_captures_stage5: assert property (
        @(posedge clk) disable iff (reset)
        clk_ena |=> (pipeline_reg_6 == $past(pipeline_reg_5))
    );

    // Stage 7 captures stage 6 when enabled.
    check_stage7_captures_stage6: assert property (
        @(posedge clk) disable iff (reset)
        clk_ena |=> (pipeline_reg_7 == $past(pipeline_reg_6))
    );

    // Stage 8 captures stage 7 when enabled.
    check_stage8_captures_stage7: assert property (
        @(posedge clk) disable iff (reset)
        clk_ena |=> (pipeline_reg_8 == $past(pipeline_reg_7))
    );

    // Stage 9 captures stage 8 when enabled.
    check_stage9_captures_stage8: assert property (
        @(posedge clk) disable iff (reset)
        clk_ena |=> (pipeline_reg_9 == $past(pipeline_reg_8))
    );

    // Stage 10 captures stage 9 when enabled.
    check_stage10_captures_stage9: assert property (
        @(posedge clk) disable iff (reset)
        clk_ena |=> (pipeline_reg_10 == $past(pipeline_reg_9))
    );

    // Stage 11 captures stage 10 when enabled.
    check_stage11_captures_stage10: assert property (
        @(posedge clk) disable iff (reset)
        clk_ena |=> (pipeline_reg_11 == $past(pipeline_reg_10))
    );

    // Stage 12 captures stage 11 when enabled.
    check_stage12_captures_stage11: assert property (
        @(posedge clk) disable iff (reset)
        clk_ena |=> (pipeline_reg_12 == $past(pipeline_reg_11))
    );

    // Stage 13 captures stage 12 when enabled.
    check_stage13_captures_stage12: assert property (
        @(posedge clk) disable iff (reset)
        clk_ena |=> (pipeline_reg_13 == $past(pipeline_reg_12))
    );

    // Stage 14 captures stage 13 when enabled.
    check_stage14_captures_stage13: assert property (
        @(posedge clk) disable iff (reset)
        clk_ena |=> (pipeline_reg_14 == $past(pipeline_reg_13))
    );

    // Stage 15 captures stage 14 when enabled.
    check_stage15_captures_stage14: assert property (
        @(posedge clk) disable iff (reset)
        clk_ena |=> (pipeline_reg_15 == $past(pipeline_reg_14))
    );

    // Stage 16 captures stage 15 when enabled.
    check_stage16_captures_stage15: assert property (
        @(posedge clk) disable iff (reset)
        clk_ena |=> (pipeline_reg_16 == $past(pipeline_reg_15))
    );

endmodule