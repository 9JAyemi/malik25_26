module comparator_sva (
    input logic [7:0] A,
    input logic [7:0] B,
    input logic EQ,
    input logic GT,
    input logic clk,
    input logic [7:0] A_reg,
    input logic [7:0] B_reg,
    input logic [2:0] stage
);

    // Stage 0 captures the current inputs.
    check_stage0_captures_inputs: assert property (
        @(posedge clk)
        (stage === 3'd0) |=> (stage === 3'd1 && A_reg === $past(A) && B_reg === $past(B))
    );

    // Stage 0 does not change the outputs.
    check_stage0_holds_outputs: assert property (
        @(posedge clk)
        (stage === 3'd0) |=> (EQ === $past(EQ) && GT === $past(GT))
    );

    // Stage 1 advances and keeps the captured operands stable.
    check_stage1_advances_and_holds_operands: assert property (
        @(posedge clk)
        (stage === 3'd1) |=> (stage === 3'd2 && A_reg === $past(A_reg) && B_reg === $past(B_reg))
    );

    // Equal captured operands set EQ and clear GT.
    check_stage1_equal_result: assert property (
        @(posedge clk)
        (stage === 3'd1 && ((A_reg == B_reg) === 1'b1))
        |=> (stage === 3'd2 && EQ === 1'b1 && GT === 1'b0)
    );

    // Greater captured operands clear EQ and set GT.
    check_stage1_greater_result: assert property (
        @(posedge clk)
        (stage === 3'd1 && ((A_reg == B_reg) !== 1'b1) && ((A_reg > B_reg) === 1'b1))
        |=> (stage === 3'd2 && EQ === 1'b0 && GT === 1'b1)
    );

    // The stage 1 else path clears both outputs.
    check_stage1_else_result: assert property (
        @(posedge clk)
        (stage === 3'd1 && ((A_reg == B_reg) !== 1'b1) && ((A_reg > B_reg) !== 1'b1))
        |=> (stage === 3'd2 && EQ === 1'b0 && GT === 1'b0)
    );

    // Stage 2 clears the outputs and returns to stage 0.
    check_stage2_clears_outputs_and_wraps: assert property (
        @(posedge clk)
        (stage === 3'd2) |=> (stage === 3'd0 && EQ === 1'b0 && GT === 1'b0 &&
                              A_reg === $past(A_reg) && B_reg === $past(B_reg))
    );

    // Unhandled stage values leave all state unchanged.
    check_invalid_stage_holds_state: assert property (
        @(posedge clk)
        (stage !== 3'd0 && stage !== 3'd1 && stage !== 3'd2)
        |=> (stage === $past(stage) && A_reg === $past(A_reg) && B_reg === $past(B_reg) &&
             EQ === $past(EQ) && GT === $past(GT))
    );

endmodule

bind comparator comparator_sva comparator_sva_inst (
    .A(A),
    .B(B),
    .EQ(EQ),
    .GT(GT),
    .clk(clk),
    .A_reg(A_reg),
    .B_reg(B_reg),
    .stage(stage)
);