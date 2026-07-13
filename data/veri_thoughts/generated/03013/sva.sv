module ring_oscillator_sva (
    input wire clk,
    input wire in,
    input wire out,
    input wire stage1,
    input wire stage2,
    input wire stage3,
    input wire stage4,
    input wire stage5
);

    // First inverter stage complements the module input.
    check_stage1_inverts_input: assert property (
        @(posedge clk) stage1 == ~in
    );

    // Second inverter stage complements stage1.
    check_stage2_inverts_stage1: assert property (
        @(posedge clk) stage2 == ~stage1
    );

    // Third inverter stage complements stage2.
    check_stage3_inverts_stage2: assert property (
        @(posedge clk) stage3 == ~stage2
    );

    // Fourth inverter stage complements stage3.
    check_stage4_inverts_stage3: assert property (
        @(posedge clk) stage4 == ~stage3
    );

    // Fifth inverter stage complements stage4.
    check_stage5_inverts_stage4: assert property (
        @(posedge clk) stage5 == ~stage4
    );

    // Output is wired directly to the fifth stage.
    check_out_matches_stage5: assert property (
        @(posedge clk) out == stage5
    );

    // End-to-end behavior is an inversion of the input.
    check_out_inverts_input: assert property (
        @(posedge clk) out == ~in
    );

endmodule