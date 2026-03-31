module add_sub_sva (
    input logic [3:0] A,
    input logic [3:0] B,
    input logic       SUB,
    input logic [3:0] OUT
);

    // OUT must match the selected add or subtract operation.
    check_selected_operation: assert property (
        @($global_clock) OUT == (SUB ? (B - A) : (A + B))
    );

    // When SUB is low, OUT must be the 4-bit sum of A and B.
    check_add_mode: assert property (
        @($global_clock) !SUB |-> (OUT == (A + B))
    );

    // When SUB is high, OUT must be the 4-bit difference of B and A.
    check_sub_mode: assert property (
        @($global_clock) SUB |-> (OUT == (B - A))
    );

    // If both inputs and SUB are stable, OUT must remain stable.
    check_stable_when_inputs_stable: assert property (
        @($global_clock) $stable({A, B, SUB}) |-> $stable(OUT)
    );

    // With SUB low and A stable, a stable B must keep OUT stable.
    check_add_b_stable_keeps_out_stable: assert property (
        @($global_clock) (!SUB && $stable(A) && $stable(B)) |-> $stable(OUT)
    );

    // With SUB high and B stable, a stable A must keep OUT stable.
    check_sub_a_stable_keeps_out_stable: assert property (
        @($global_clock) (SUB && $stable(B) && $stable(A)) |-> $stable(OUT)
    );

    // With SUB low and B stable, a stable A must keep OUT stable.
    check_add_a_stable_keeps_out_stable: assert property (
        @($global_clock) (!SUB && $stable(A) && $stable(B)) |-> $stable(OUT)
    );

    // With SUB high and A stable, a stable B must keep OUT stable.
    check_sub_b_stable_keeps_out_stable: assert property (
        @($global_clock) (SUB && $stable(B) && $stable(A)) |-> $stable(OUT)
    );

endmodule