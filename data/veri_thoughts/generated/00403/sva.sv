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
    input logic reset
);

    // Reset forces all pipeline registers to zero.
    check_reset_clears_pipeline: assert property (
        @(posedge clk)
        reset |-> ((pipeline_reg_0 == '0) &&
                   (pipeline_reg_1 == '0) &&
                   (pipeline_reg_2 == '0) &&
                   (pipeline_reg_3 == '0) &&
                   (pipeline_reg_4 == '0) &&
                   (pipeline_reg_5 == '0) &&
                   (pipeline_reg_6 == '0) &&
                   (pipeline_reg_7 == '0) &&
                   (pipeline_reg_8 == '0) &&
                   (pipeline_reg_9 == '0))
    );

    // Enabled clock loads stage 0 from the input stream.
    check_stage0_captures_input: assert property (
        @(posedge clk) disable iff (reset)
        clk_ena |=> (pipeline_reg_0 == $past(in_stream))
    );

    // Enabled clock shifts stage 0 into stage 1.
    check_stage1_shifts_stage0: assert property (
        @(posedge clk) disable iff (reset)
        clk_ena |=> (pipeline_reg_1 == $past(pipeline_reg_0))
    );

    // Enabled clock shifts stage 1 into stage 2.
    check_stage2_shifts_stage1: assert property (
        @(posedge clk) disable iff (reset)
        clk_ena |=> (pipeline_reg_2 == $past(pipeline_reg_1))
    );

    // Enabled clock shifts stage 2 into stage 3.
    check_stage3_shifts_stage2: assert property (
        @(posedge clk) disable iff (reset)
        clk_ena |=> (pipeline_reg_3 == $past(pipeline_reg_2))
    );

    // Enabled clock shifts stage 3 into stage 4.
    check_stage4_shifts_stage3: assert property (
        @(posedge clk) disable iff (reset)
        clk_ena |=> (pipeline_reg_4 == $past(pipeline_reg_3))
    );

    // Enabled clock shifts stage 4 into stage 5.
    check_stage5_shifts_stage4: assert property (
        @(posedge clk) disable iff (reset)
        clk_ena |=> (pipeline_reg_5 == $past(pipeline_reg_4))
    );

    // Enabled clock shifts stage 5 into stage 6.
    check_stage6_shifts_stage5: assert property (
        @(posedge clk) disable iff (reset)
        clk_ena |=> (pipeline_reg_6 == $past(pipeline_reg_5))
    );

    // Enabled clock shifts stage 6 into stage 7.
    check_stage7_shifts_stage6: assert property (
        @(posedge clk) disable iff (reset)
        clk_ena |=> (pipeline_reg_7 == $past(pipeline_reg_6))
    );

    // Enabled clock shifts stage 7 into stage 8.
    check_stage8_shifts_stage7: assert property (
        @(posedge clk) disable iff (reset)
        clk_ena |=> (pipeline_reg_8 == $past(pipeline_reg_7))
    );

    // Enabled clock shifts stage 8 into stage 9.
    check_stage9_shifts_stage8: assert property (
        @(posedge clk) disable iff (reset)
        clk_ena |=> (pipeline_reg_9 == $past(pipeline_reg_8))
    );

    // Disabled clock enable holds all pipeline registers.
    check_hold_when_clk_ena_low: assert property (
        @(posedge clk) disable iff (reset)
        !clk_ena |=> ((pipeline_reg_0 == $past(pipeline_reg_0)) &&
                      (pipeline_reg_1 == $past(pipeline_reg_1)) &&
                      (pipeline_reg_2 == $past(pipeline_reg_2)) &&
                      (pipeline_reg_3 == $past(pipeline_reg_3)) &&
                      (pipeline_reg_4 == $past(pipeline_reg_4)) &&
                      (pipeline_reg_5 == $past(pipeline_reg_5)) &&
                      (pipeline_reg_6 == $past(pipeline_reg_6)) &&
                      (pipeline_reg_7 == $past(pipeline_reg_7)) &&
                      (pipeline_reg_8 == $past(pipeline_reg_8)) &&
                      (pipeline_reg_9 == $past(pipeline_reg_9)))
    );

endmodule