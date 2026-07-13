module magnitude_comparator_4bit_assertions (
    input logic [3:0] A,
    input logic [3:0] B,
    input logic clk,
    input logic EQ,
    input logic GT,
    input logic LT,
    input logic [3:0] A_reg,
    input logic [3:0] B_reg,
    input logic [2:0] stage,
    input logic [3:0] A_next,
    input logic [3:0] B_next,
    input logic EQ_next,
    input logic GT_next,
    input logic LT_next
);

    // Stage 0 captures inputs and advances to stage 1.
    check_stage0_captures_inputs: assert property (
        @(posedge clk)
        (stage == 3'd0)
        |=> (stage == 3'd1) &&
            (A_reg == $past(A)) &&
            (B_reg == $past(B))
    );

    // Stage 1 sorts the captured registers and advances to stage 2.
    check_stage1_sorts_registers: assert property (
        @(posedge clk)
        (stage == 3'd1)
        |=> (stage == 3'd2) &&
            (A_reg == (($past(A_reg) > $past(B_reg)) ? $past(A_reg) : $past(B_reg))) &&
            (B_reg == (($past(A_reg) > $past(B_reg)) ? $past(B_reg) : $past(A_reg)))
    );

    // Stage 2 returns to stage 0 and leaves the registers unchanged.
    check_stage2_returns_to_stage0: assert property (
        @(posedge clk)
        (stage == 3'd2)
        |=> (stage == 3'd0) &&
            (A_reg == $past(A_reg)) &&
            (B_reg == $past(B_reg))
    );

    // Unhandled stage values hold state because the case has no default.
    check_invalid_stage_holds_state: assert property (
        @(posedge clk)
        (stage != 3'd0 && stage != 3'd1 && stage != 3'd2)
        |=> (stage == $past(stage)) &&
            (A_reg == $past(A_reg)) &&
            (B_reg == $past(B_reg))
    );

    // Outputs are forced low unless stage 2 is active.
    check_outputs_low_outside_stage2: assert property (
        @(posedge clk)
        (stage != 3'd2)
        |-> (EQ == 1'b0) &&
             (GT == 1'b0) &&
             (LT == 1'b0)
    );

    // In stage 2, outputs report equality or difference of the current registers.
    check_stage2_outputs_match_register_relation: assert property (
        @(posedge clk)
        (stage == 3'd2)
        |-> (EQ == (A_reg == B_reg)) &&
             (GT == (A_reg != B_reg)) &&
             (LT == 1'b0)
    );

    // LT is never asserted by this implementation.
    check_lt_output_always_low: assert property (
        @(posedge clk)
        (LT == 1'b0)
    );

    // A_next is the larger of A_reg and B_reg.
    check_a_next_is_max_of_registers: assert property (
        @(posedge clk)
        A_next == ((A_reg > B_reg) ? A_reg : B_reg)
    );

    // B_next is the smaller of A_reg and B_reg.
    check_b_next_is_min_of_registers: assert property (
        @(posedge clk)
        B_next == ((A_reg > B_reg) ? B_reg : A_reg)
    );

    // The next compare flags encode only equal or greater-than.
    check_compare_next_flags_match_relation: assert property (
        @(posedge clk)
        (EQ_next == (A_reg == B_reg)) &&
        (GT_next == (A_reg != B_reg)) &&
        (LT_next == 1'b0)
    );

endmodule