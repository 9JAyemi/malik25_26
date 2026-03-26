module decoder_4to16_pipeline_assertions (
    input logic        A,
    input logic        B,
    input logic [15:0] Y,
    input logic [1:0]  stage1_A,
    input logic [1:0]  stage1_B,
    input logic [3:0]  stage2_A,
    input logic [3:0]  stage2_B,
    input logic [7:0]  stage3_A,
    input logic [7:0]  stage3_B
);

    // Stage1 A captures the current A value with zero extension after input activity.
    check_stage1_a_capture: assert property (
        @($global_clock)
        ($changed(A) || $changed(B)) |=> ##[0:1] (stage1_A === {1'b0, A})
    );

    // Stage1 B captures the current B value with zero extension after input activity.
    check_stage1_b_capture: assert property (
        @($global_clock)
        ($changed(A) || $changed(B)) |=> ##[0:1] (stage1_B === {1'b0, B})
    );

    // Stage2 A captures the current stage1_A value with zero extension.
    check_stage2_a_capture: assert property (
        @($global_clock)
        ($changed(stage1_A) || $changed(stage1_B)) |=> ##[0:1] (stage2_A === {2'b00, stage1_A})
    );

    // Stage2 B captures the current stage1_B value with zero extension.
    check_stage2_b_capture: assert property (
        @($global_clock)
        ($changed(stage1_A) || $changed(stage1_B)) |=> ##[0:1] (stage2_B === {2'b00, stage1_B})
    );

    // Stage3 A captures the current stage2_A value with zero extension.
    check_stage3_a_capture: assert property (
        @($global_clock)
        ($changed(stage2_A) || $changed(stage2_B)) |=> ##[0:1] (stage3_A === {4'b0000, stage2_A})
    );

    // Stage3 B captures the current stage2_B value with zero extension.
    check_stage3_b_capture: assert property (
        @($global_clock)
        ($changed(stage2_A) || $changed(stage2_B)) |=> ##[0:1] (stage3_B === {4'b0000, stage2_B})
    );

    // Input activity eventually drives stage3_A to the zero-extended A value.
    check_stage3_a_from_input: assert property (
        @($global_clock)
        ($changed(A) || $changed(B)) |=> ##[0:3] (stage3_A === {7'b0000000, A})
    );

    // Input activity eventually drives stage3_B to the zero-extended B value.
    check_stage3_b_from_input: assert property (
        @($global_clock)
        ($changed(A) || $changed(B)) |=> ##[0:3] (stage3_B === {7'b0000000, B})
    );

    // When A is 0, input activity eventually produces the bit-0 decode output.
    check_decode_for_a_zero: assert property (
        @($global_clock)
        ($changed(A) || $changed(B)) && (A === 1'b0) |=> ##[0:4] (Y === 16'h0001)
    );

    // When A is 1, input activity eventually produces the bit-1 decode output.
    check_decode_for_a_one: assert property (
        @($global_clock)
        ($changed(A) || $changed(B)) && (A === 1'b1) |=> ##[0:4] (Y === 16'h0002)
    );

endmodule