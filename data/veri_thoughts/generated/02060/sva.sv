module d_ff_pipeline_sva (
    input logic clk,
    input logic d,
    input logic q,
    input logic t1,
    input logic t2
);
    // Clock: clk (posedge). Reset: none. Logic: sequential 3-stage pipeline.
    // Behavior: t1<=d; t2<=t1; q<=t2; hence at sampling q==$past(d,3).

    // t1 captures d with 1-cycle latency (sampled semantics).
    check_stage1_capture: assert property (
        @(posedge clk) $past(1'b1,1) |-> (t1 == $past(d,1))
    );

    // t2 captures t1 with 1-cycle latency.
    check_stage2_capture: assert property (
        @(posedge clk) $past(1'b1,1) |-> (t2 == $past(t1,1))
    );

    // q captures t2 with 1-cycle latency.
    check_stage3_capture: assert property (
        @(posedge clk) $past(1'b1,1) |-> (q == $past(t2,1))
    );

    // t2 equals d delayed by 2 cycles.
    check_t2_equals_d_2cycle: assert property (
        @(posedge clk) $past(1'b1,2) |-> (t2 == $past(d,2))
    );

    // q equals t1 delayed by 2 cycles.
    check_q_equals_t1_2cycle: assert property (
        @(posedge clk) $past(1'b1,2) |-> (q == $past(t1,2))
    );

    // q equals d delayed by 3 cycles.
    check_q_equals_d_3cycle: assert property (
        @(posedge clk) $past(1'b1,3) |-> (q == $past(d,3))
    );

endmodule