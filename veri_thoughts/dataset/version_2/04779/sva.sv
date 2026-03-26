module my_nand_gate_sva (
    input logic Y,
    input logic A,
    input logic B,
    input logic C,
    input logic D
);

    // Y matches the implemented gate-level function.
    check_y_function: assert property (
        @($global_clock) Y == ~((A & B) | (C & D))
    );

    // A and B high force the output low.
    check_ab_pair_forces_low: assert property (
        @($global_clock) (A & B) |-> !Y
    );

    // C and D high force the output low.
    check_cd_pair_forces_low: assert property (
        @($global_clock) (C & D) |-> !Y
    );

    // If neither input pair is fully high, the output is high.
    check_no_active_pair_drives_high: assert property (
        @($global_clock) (!(A & B) && !(C & D)) |-> Y
    );

    // All inputs low produce a high output.
    check_all_inputs_low_case: assert property (
        @($global_clock) (!A && !B && !C && !D) |-> Y
    );

    // All inputs high produce a low output.
    check_all_inputs_high_case: assert property (
        @($global_clock) (A && B && C && D) |-> !Y
    );

endmodule