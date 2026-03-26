module counter_sva (
    input logic       clk,
    input logic       reset,
    input logic [3:0] out,
    input logic [3:0] pipeline_reg1,
    input logic [3:0] pipeline_reg2,
    input logic [3:0] pipeline_reg3
);

    // Reset clears all registers on the next clock.
    check_reset_clears_state: assert property (
        @(posedge clk)
        reset |=> (pipeline_reg1 == 4'b0) &&
                  (pipeline_reg2 == 4'b0) &&
                  (pipeline_reg3 == 4'b0) &&
                  (out == 4'b0)
    );

    // State is all zero immediately after a reset cycle.
    check_post_reset_zero_state: assert property (
        @(posedge clk) disable iff (reset)
        $past(reset) |-> (pipeline_reg1 == 4'b0) &&
                         (pipeline_reg2 == 4'b0) &&
                         (pipeline_reg3 == 4'b0) &&
                         (out == 4'b0)
    );

    // The first active cycle after reset produces out=1 with zeroed pipeline.
    check_first_active_cycle_after_reset: assert property (
        @(posedge clk) disable iff (reset)
        $fell(reset) |=> (pipeline_reg1 == 4'b0) &&
                         (pipeline_reg2 == 4'b0) &&
                         (pipeline_reg3 == 4'b0) &&
                         (out == 4'b1)
    );

    // pipeline_reg1 captures the previous out value.
    check_pipeline_reg1_captures_out: assert property (
        @(posedge clk) disable iff (reset)
        !$past(reset) |-> (pipeline_reg1 == $past(out))
    );

    // pipeline_reg2 captures the previous pipeline_reg1 value.
    check_pipeline_reg2_captures_reg1: assert property (
        @(posedge clk) disable iff (reset)
        !$past(reset) |-> (pipeline_reg2 == $past(pipeline_reg1))
    );

    // pipeline_reg3 captures the previous pipeline_reg2 value.
    check_pipeline_reg3_captures_reg2: assert property (
        @(posedge clk) disable iff (reset)
        !$past(reset) |-> (pipeline_reg3 == $past(pipeline_reg2))
    );

    // out updates from the previous pipeline_reg3 value plus one.
    check_out_updates_from_pipeline_reg3: assert property (
        @(posedge clk) disable iff (reset)
        !$past(reset) |-> (out == ($past(pipeline_reg3) + 4'd1))
    );

    // After two active cycles, pipeline_reg2 matches out from two cycles earlier.
    check_pipeline_reg2_two_cycle_delay: assert property (
        @(posedge clk) disable iff (reset)
        (!$past(reset,1) && !$past(reset,2)) |-> (pipeline_reg2 == $past(out,2))
    );

    // After three active cycles, pipeline_reg3 matches out from three cycles earlier.
    check_pipeline_reg3_three_cycle_delay: assert property (
        @(posedge clk) disable iff (reset)
        (!$past(reset,1) && !$past(reset,2) && !$past(reset,3)) |-> (pipeline_reg3 == $past(out,3))
    );

    // After four active cycles, out matches out from four cycles earlier plus one.
    check_out_four_cycle_recurrence: assert property (
        @(posedge clk) disable iff (reset)
        (!$past(reset,1) && !$past(reset,2) && !$past(reset,3) && !$past(reset,4)) |-> (out == ($past(out,4) + 4'd1))
    );

endmodule