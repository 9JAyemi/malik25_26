module addsub_sva (
    input logic        clk,
    input logic [15:0] A,
    input logic [15:0] B,
    input logic        C,
    input logic [15:0] Q
);

    // Q must match the selected add or subtract operation.
    check_q_matches_selected_operation: assert property (
        @(posedge clk) Q == (C ? (A - B) : (A + B))
    );

    // When C is low, Q must be the 16-bit sum of A and B.
    check_add_mode_result: assert property (
        @(posedge clk) !C |-> (Q == (A + B))
    );

    // When C is high, Q must be the 16-bit difference of A and B.
    check_sub_mode_result: assert property (
        @(posedge clk) C |-> (Q == (A - B))
    );

    // If A and B are stable, a stable C must keep Q stable.
    check_q_stable_when_inputs_stable: assert property (
        @(posedge clk) ($stable(A) && $stable(B) && $stable(C)) |-> $stable(Q)
    );

    // In add mode, a stable A and B must keep Q stable.
    check_add_mode_stable_when_operands_stable: assert property (
        @(posedge clk) (!C && $stable(A) && $stable(B)) |-> $stable(Q)
    );

    // In subtract mode, a stable A and B must keep Q stable.
    check_sub_mode_stable_when_operands_stable: assert property (
        @(posedge clk) (C && $stable(A) && $stable(B)) |-> $stable(Q)
    );

endmodule