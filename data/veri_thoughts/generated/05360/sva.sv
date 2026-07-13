module adder_assertions (
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [3:0] S,
    input logic C
);

    // Carry and sum must match the 5-bit addition of A and B.
    check_add_result: assert property (
        @($global_clock) {C, S} == ({1'b0, A} + {1'b0, B})
    );

    // Carry must indicate overflow beyond 4 bits.
    check_carry_overflow: assert property (
        @($global_clock) C == (({1'b0, A} + {1'b0, B}) > 5'd15)
    );

    // Adding zero on A must pass B through with no carry.
    check_zero_a_identity: assert property (
        @($global_clock) (A == 4'h0) |-> (S == B && C == 1'b0)
    );

    // Adding zero on B must pass A through with no carry.
    check_zero_b_identity: assert property (
        @($global_clock) (B == 4'h0) |-> (S == A && C == 1'b0)
    );

    // Maximum operands must produce the expected overflowed result.
    check_max_operands: assert property (
        @($global_clock) (A == 4'hF && B == 4'hF) |-> (C == 1'b1 && S == 4'hE)
    );

    // If inputs do not change, outputs must also remain unchanged.
    check_stable_inputs_hold_outputs: assert property (
        @($global_clock) ($stable(A) && $stable(B)) |-> ($stable(S) && $stable(C))
    );

    // Any observed output change must be caused by an input change.
    check_output_change_requires_input_change: assert property (
        @($global_clock) ($changed(S) || $changed(C)) |-> ($changed(A) || $changed(B))
    );

endmodule