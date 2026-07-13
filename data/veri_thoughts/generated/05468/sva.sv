module adder_sva (
    input logic [31:0] A,
    input logic [31:0] B,
    input logic [31:0] C,
    input logic [31:0] D,
    input logic [31:0] Y
);

    // Y must equal the sum of all four inputs.
    check_sum_exact: assert property (
        @($global_clock) Y == (A + B + C + D)
    );

    // Stable inputs must keep Y stable.
    check_output_stable_when_inputs_stable: assert property (
        @($global_clock) ($stable(A) && $stable(B) && $stable(C) && $stable(D)) |-> $stable(Y)
    );

    // All-zero inputs must produce zero output.
    check_zero_inputs_zero_output: assert property (
        @($global_clock) ((A == 32'h00000000) && (B == 32'h00000000) && (C == 32'h00000000) && (D == 32'h00000000)) |-> (Y == 32'h00000000)
    );

    // With only A active, Y must match A.
    check_a_pass_through_when_others_zero: assert property (
        @($global_clock) ((B == 32'h00000000) && (C == 32'h00000000) && (D == 32'h00000000)) |-> (Y == A)
    );

    // With only B active, Y must match B.
    check_b_pass_through_when_others_zero: assert property (
        @($global_clock) ((A == 32'h00000000) && (C == 32'h00000000) && (D == 32'h00000000)) |-> (Y == B)
    );

    // With only C active, Y must match C.
    check_c_pass_through_when_others_zero: assert property (
        @($global_clock) ((A == 32'h00000000) && (B == 32'h00000000) && (D == 32'h00000000)) |-> (Y == C)
    );

    // With only D active, Y must match D.
    check_d_pass_through_when_others_zero: assert property (
        @($global_clock) ((A == 32'h00000000) && (B == 32'h00000000) && (C == 32'h00000000)) |-> (Y == D)
    );

endmodule