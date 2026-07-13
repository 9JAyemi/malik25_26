module top_module_sva (
    input logic clk,
    input logic reset,
    input logic up_down,
    input logic [2:0] q,
    input logic [2:0] q_internal
);

    // Top-level output matches the internal counter output.
    check_output_mirrors_internal: assert property (
        @(posedge clk) disable iff (reset) (q == q_internal)
    );

    // Reset forces the internal counter to zero.
    check_reset_clears_internal: assert property (
        @(posedge clk) reset |-> (q_internal == 3'b000)
    );

    // Reset forces the top-level output to zero.
    check_reset_clears_output: assert property (
        @(posedge clk) reset |-> (q == 3'b000)
    );

    // The first sampled cycle after reset still sees zero internally.
    check_post_reset_internal_zero: assert property (
        @(posedge clk) disable iff (reset)
        (!$initstate && $past(reset)) |-> (q_internal == 3'b000)
    );

    // A nonzero state after an up cycle must be the incremented value.
    check_up_step_when_nonzero: assert property (
        @(posedge clk) disable iff (reset)
        (!$initstate && (q_internal != 3'b000) && $past(!reset && up_down))
        |-> (q_internal == ($past(q_internal) + 3'b001))
    );

    // A nonzero state after a down cycle must be the decremented value.
    check_down_step_when_nonzero: assert property (
        @(posedge clk) disable iff (reset)
        (!$initstate && (q_internal != 3'b000) && $past(!reset && !up_down))
        |-> (q_internal == ($past(q_internal) - 3'b001))
    );

    // Up counting wraps from seven to zero.
    check_up_wrap_to_zero: assert property (
        @(posedge clk) disable iff (reset)
        (!$initstate && $past(!reset && up_down) && ($past(q_internal) == 3'b111))
        |-> (q_internal == 3'b000)
    );

    // Down counting from one reaches zero.
    check_down_from_one_to_zero: assert property (
        @(posedge clk) disable iff (reset)
        (!$initstate && $past(!reset && !up_down) && ($past(q_internal) == 3'b001))
        |-> (q_internal == 3'b000)
    );

endmodule