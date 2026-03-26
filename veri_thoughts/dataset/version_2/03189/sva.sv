module nor4b_with_inverting_input_sva (
    input logic Y,
    input logic A,
    input logic B,
    input logic C,
    input logic D_N
);

    // No RTL clock or reset; sample the combinational logic on the global clock.

    // Y must equal the NOR of A, B, C, and the inversion of D_N.
    check_canonical_function: assert property (
        @($global_clock) Y == ~(A | B | C | ~D_N)
    );

    // Y can only be HIGH when A, B, and C are LOW and D_N is HIGH.
    check_high_output_only_under_valid_inputs: assert property (
        @($global_clock) Y |-> (!A && !B && !C && D_N)
    );

    // Y must be HIGH when A, B, and C are LOW and D_N is HIGH.
    check_high_output_when_all_inputs_allow_it: assert property (
        @($global_clock) (!A && !B && !C && D_N) |-> Y
    );

    // A HIGH input forces the NOR output LOW.
    check_a_high_forces_low: assert property (
        @($global_clock) A |-> !Y
    );

    // B HIGH input forces the NOR output LOW.
    check_b_high_forces_low: assert property (
        @($global_clock) B |-> !Y
    );

    // C HIGH input forces the NOR output LOW.
    check_c_high_forces_low: assert property (
        @($global_clock) C |-> !Y
    );

    // A LOW D_N input is inverted before the NOR and forces the output LOW.
    check_dn_low_forces_low: assert property (
        @($global_clock) !D_N |-> !Y
    );

endmodule