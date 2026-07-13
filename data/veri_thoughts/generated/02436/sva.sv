module bitwise_and_sva (
    input logic clk,
    input signed [31:0] in1,
    input signed [31:0] in2,
    input signed [31:0] out,
    input signed [31:0] stage1_out,
    input signed [31:0] stage2_out
);
    // stage1_out must equal bitwise AND of inputs at all times.
    check_stage1_is_and: assert property (
        @(posedge clk) stage1_out == (in1 & in2)
    );

    // stage2_out must follow stage1_out.
    check_stage2_follows_stage1: assert property (
        @(posedge clk) stage2_out == stage1_out
    );

    // out must follow stage2_out.
    check_out_follows_stage2: assert property (
        @(posedge clk) out == stage2_out
    );

    // out must equal bitwise AND of inputs.
    check_out_is_and: assert property (
        @(posedge clk) out == (in1 & in2)
    );

    // If inputs are stable, out remains stable.
    check_stable_inputs_keep_out_stable: assert property (
        @(posedge clk) ($stable(in1) && $stable(in2)) |-> $stable(out)
    );

    // If stage1_out is stable, stage2_out remains stable.
    check_stage1_stable_implies_stage2_stable: assert property (
        @(posedge clk) $stable(stage1_out) |-> $stable(stage2_out)
    );

    // If stage2_out is stable, out remains stable.
    check_stage2_stable_implies_out_stable: assert property (
        @(posedge clk) $stable(stage2_out) |-> $stable(out)
    );

    // A change on out implies at least one input changed.
    check_out_change_implies_input_change: assert property (
        @(posedge clk) $changed(out) |-> ($changed(in1) || $changed(in2))
    );

    // A change on stage2_out implies stage1_out changed.
    check_stage2_change_implies_stage1_change: assert property (
        @(posedge clk) $changed(stage2_out) |-> $changed(stage1_out)
    );

    // A change on stage1_out implies at least one input changed.
    check_stage1_change_implies_input_change: assert property (
        @(posedge clk) $changed(stage1_out) |-> ($changed(in1) || $changed(in2))
    );
endmodule