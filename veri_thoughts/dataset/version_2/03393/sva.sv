module bitwise_or_sva (
    input logic [3:0] a,
    input logic [3:0] b,
    input logic clk,
    input logic [3:0] out,
    input logic [3:0] stage1_out,
    input logic [3:0] stage2_out
);

    // stage1_out captures the bitwise OR of a and b from the prior clock.
    check_stage1_or_capture: assert property (
        @(posedge clk) 1'b1 |=> (stage1_out == ($past(a) | $past(b)))
    );

    // stage2_out captures the prior value of stage1_out.
    check_stage2_pipeline_capture: assert property (
        @(posedge clk) 1'b1 |=> (stage2_out == $past(stage1_out))
    );

    // out always mirrors stage2_out.
    check_out_matches_stage2: assert property (
        @(posedge clk) (out == stage2_out)
    );

    // out reflects the OR of a and b from two clocks earlier.
    check_out_two_cycle_latency: assert property (
        @(posedge clk) 1'b1 |=> ##1 (out == ($past(a, 2) | $past(b, 2)))
    );

endmodule