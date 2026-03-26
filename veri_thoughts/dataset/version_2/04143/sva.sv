module add_sub_4bit_sva (
    input logic       clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic       SUB,
    input logic [3:0] SUM
);

    // In add mode, SUM matches A + B.
    check_add_mode_result: assert property (
        @(posedge clk) (SUB == 1'b0) |-> (SUM == (A + B))
    );

    // In subtract mode, SUM matches A - B.
    check_sub_mode_result: assert property (
        @(posedge clk) (SUB == 1'b1) |-> (SUM == (A - B))
    );

    // With B equal to zero, SUM must equal A in either mode.
    check_zero_b_identity: assert property (
        @(posedge clk) (B == 4'b0000) |-> (SUM == A)
    );

    // In subtract mode, equal operands must produce zero.
    check_sub_equal_operands_zero: assert property (
        @(posedge clk) (SUB == 1'b1 && A == B) |-> (SUM == 4'b0000)
    );

    // If all inputs are stable, the output must remain stable.
    check_stable_inputs_keep_sum_stable: assert property (
        @(posedge clk) $stable({A, B, SUB}) |-> $stable(SUM)
    );

endmodule