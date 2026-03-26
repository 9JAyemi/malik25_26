module sky130_fd_sc_ms__xor3_sva (
    input logic A,
    input logic B,
    input logic C,
    input logic X
);

    // X must equal the inverted three-input XOR of A, B, and C.
    check_inverted_xor3_function: assert property (
        @($global_clock) X == ~(A ^ B ^ C)
    );

    // Even input parity must drive X high.
    check_even_parity_drives_high: assert property (
        @($global_clock) !(A ^ B ^ C) |-> X
    );

    // Odd input parity must drive X low.
    check_odd_parity_drives_low: assert property (
        @($global_clock) (A ^ B ^ C) |-> !X
    );

    // If all inputs are stable, the output must remain stable.
    check_stable_inputs_hold_output: assert property (
        @($global_clock) $stable({A, B, C}) |-> $stable(X)
    );

    // Toggling only A must toggle X.
    check_toggle_a_flips_output: assert property (
        @($global_clock) ($changed(A) && $stable({B, C})) |-> $changed(X)
    );

    // Toggling only B must toggle X.
    check_toggle_b_flips_output: assert property (
        @($global_clock) ($changed(B) && $stable({A, C})) |-> $changed(X)
    );

    // Toggling only C must toggle X.
    check_toggle_c_flips_output: assert property (
        @($global_clock) ($changed(C) && $stable({A, B})) |-> $changed(X)
    );

    // Toggling A and B together must leave X unchanged.
    check_toggle_ab_holds_output: assert property (
        @($global_clock) ($changed(A) && $changed(B) && $stable(C)) |-> $stable(X)
    );

    // Toggling A and C together must leave X unchanged.
    check_toggle_ac_holds_output: assert property (
        @($global_clock) ($changed(A) && $changed(C) && $stable(B)) |-> $stable(X)
    );

    // Toggling B and C together must leave X unchanged.
    check_toggle_bc_holds_output: assert property (
        @($global_clock) ($changed(B) && $changed(C) && $stable(A)) |-> $stable(X)
    );

endmodule