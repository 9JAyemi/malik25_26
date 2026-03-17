module input_pipeline_sva #(
    parameter WIDTH = 1
) (
    input logic clk,
    input logic clk_ena,
    input logic [WIDTH-1:0] in_stream,
    input logic [WIDTH-1:0] pipeline_reg_0,
    input logic [WIDTH-1:0] pipeline_reg_1,
    input logic [WIDTH-1:0] pipeline_reg_2,
    input logic [WIDTH-1:0] pipeline_reg_3,
    input logic [WIDTH-1:0] pipeline_reg_4,
    input logic [WIDTH-1:0] pipeline_reg_5,
    input logic [WIDTH-1:0] pipeline_reg_6,
    input logic [WIDTH-1:0] pipeline_reg_7,
    input logic [WIDTH-1:0] pipeline_reg_8,
    input logic [WIDTH-1:0] pipeline_reg_9,
    input logic [WIDTH-1:0] pipeline_reg_10,
    input logic [WIDTH-1:0] pipeline_reg_11,
    input logic reset
);

    // Reset clears all pipeline stages by the next clock.
    check_reset_clears_pipeline: assert property (
        @(posedge clk)
        (!$initstate && $past(reset)) |-> (
            {pipeline_reg_11, pipeline_reg_10, pipeline_reg_9, pipeline_reg_8,
             pipeline_reg_7, pipeline_reg_6, pipeline_reg_5, pipeline_reg_4,
             pipeline_reg_3, pipeline_reg_2, pipeline_reg_1, pipeline_reg_0} == '0
        )
    );

    // Stage 0 captures the input stream on enabled cycles.
    check_stage0_captures_input: assert property (
        @(posedge clk) disable iff (reset)
        (!$initstate && $past(!reset && clk_ena)) |-> (pipeline_reg_0 == $past(in_stream))
    );

    // Stage 1 shifts the prior stage 0 value on enabled cycles.
    check_stage1_shifts_forward: assert property (
        @(posedge clk) disable iff (reset)
        (!$initstate && $past(!reset && clk_ena)) |-> (pipeline_reg_1 == $past(pipeline_reg_0))
    );

    // Stage 2 shifts the prior stage 1 value on enabled cycles.
    check_stage2_shifts_forward: assert property (
        @(posedge clk) disable iff (reset)
        (!$initstate && $past(!reset && clk_ena)) |-> (pipeline_reg_2 == $past(pipeline_reg_1))
    );

    // Stage 3 shifts the prior stage 2 value on enabled cycles.
    check_stage3_shifts_forward: assert property (
        @(posedge clk) disable iff (reset)
        (!$initstate && $past(!reset && clk_ena)) |-> (pipeline_reg_3 == $past(pipeline_reg_2))
    );

    // Stage 4 shifts the prior stage 3 value on enabled cycles.
    check_stage4_shifts_forward: assert property (
        @(posedge clk) disable iff (reset)
        (!$initstate && $past(!reset && clk_ena)) |-> (pipeline_reg_4 == $past(pipeline_reg_3))
    );

    // Stage 5 shifts the prior stage 4 value on enabled cycles.
    check_stage5_shifts_forward: assert property (
        @(posedge clk) disable iff (reset)
        (!$initstate && $past(!reset && clk_ena)) |-> (pipeline_reg_5 == $past(pipeline_reg_4))
    );

    // Stage 6 shifts the prior stage 5 value on enabled cycles.
    check_stage6_shifts_forward: assert property (
        @(posedge clk) disable iff (reset)
        (!$initstate && $past(!reset && clk_ena)) |-> (pipeline_reg_6 == $past(pipeline_reg_5))
    );

    // Stage 7 shifts the prior stage 6 value on enabled cycles.
    check_stage7_shifts_forward: assert property (
        @(posedge clk) disable iff (reset)
        (!$initstate && $past(!reset && clk_ena)) |-> (pipeline_reg_7 == $past(pipeline_reg_6))
    );

    // Stage 8 shifts the prior stage 7 value on enabled cycles.
    check_stage8_shifts_forward: assert property (
        @(posedge clk) disable iff (reset)
        (!$initstate && $past(!reset && clk_ena)) |-> (pipeline_reg_8 == $past(pipeline_reg_7))
    );

    // Stage 9 shifts the prior stage 8 value on enabled cycles.
    check_stage9_shifts_forward: assert property (
        @(posedge clk) disable iff (reset)
        (!$initstate && $past(!reset && clk_ena)) |-> (pipeline_reg_9 == $past(pipeline_reg_8))
    );

    // Stage 10 shifts the prior stage 9 value on enabled cycles.
    check_stage10_shifts_forward: assert property (
        @(posedge clk) disable iff (reset)
        (!$initstate && $past(!reset && clk_ena)) |-> (pipeline_reg_10 == $past(pipeline_reg_9))
    );

    // Stage 11 shifts the prior stage 10 value on enabled cycles.
    check_stage11_shifts_forward: assert property (
        @(posedge clk) disable iff (reset)
        (!$initstate && $past(!reset && clk_ena)) |-> (pipeline_reg_11 == $past(pipeline_reg_10))
    );

    // All stages hold their values when the clock enable is low.
    check_pipeline_holds_when_disabled: assert property (
        @(posedge clk) disable iff (reset)
        (!$initstate && $past(!reset && !clk_ena)) |-> (
            {pipeline_reg_11, pipeline_reg_10, pipeline_reg_9, pipeline_reg_8,
             pipeline_reg_7, pipeline_reg_6, pipeline_reg_5, pipeline_reg_4,
             pipeline_reg_3, pipeline_reg_2, pipeline_reg_1, pipeline_reg_0} ==
            $past({pipeline_reg_11, pipeline_reg_10, pipeline_reg_9, pipeline_reg_8,
                   pipeline_reg_7, pipeline_reg_6, pipeline_reg_5, pipeline_reg_4,
                   pipeline_reg_3, pipeline_reg_2, pipeline_reg_1, pipeline_reg_0})
        )
    );

endmodule