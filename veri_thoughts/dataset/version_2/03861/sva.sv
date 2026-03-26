module and_gate_pipeline_sva(
    input logic a,
    input logic b,
    input logic clk,
    input logic out,
    input logic pipe1_out,
    input logic pipe2_out
);

    // pipe1_out goes high one cycle after a & b is high.
    check_pipe1_capture_high: assert property (
        @(posedge clk) (a & b) |=> pipe1_out
    );

    // pipe1_out goes low one cycle after a & b is low.
    check_pipe1_capture_low: assert property (
        @(posedge clk) !(a & b) |=> !pipe1_out
    );

    // pipe2_out goes high one cycle after pipe1_out is high.
    check_pipe2_capture_high: assert property (
        @(posedge clk) pipe1_out |=> pipe2_out
    );

    // pipe2_out goes low one cycle after pipe1_out is low.
    check_pipe2_capture_low: assert property (
        @(posedge clk) !pipe1_out |=> !pipe2_out
    );

    // out goes high one cycle after pipe2_out is high.
    check_out_capture_high: assert property (
        @(posedge clk) pipe2_out |=> out
    );

    // out goes low one cycle after pipe2_out is low.
    check_out_capture_low: assert property (
        @(posedge clk) !pipe2_out |=> !out
    );

    // a high AND result reaches pipe2_out after two cycles.
    check_pipe2_latency_high: assert property (
        @(posedge clk) (a & b) |=> ##1 pipe2_out
    );

    // a low AND result reaches pipe2_out after two cycles.
    check_pipe2_latency_low: assert property (
        @(posedge clk) !(a & b) |=> ##1 !pipe2_out
    );

    // a high AND result reaches out after three cycles.
    check_out_latency_high: assert property (
        @(posedge clk) (a & b) |=> ##2 out
    );

    // a low AND result reaches out after three cycles.
    check_out_latency_low: assert property (
        @(posedge clk) !(a & b) |=> ##2 !out
    );

endmodule