module my_module_sva (
    input logic Z,
    input logic A,
    input logic TE_B
);

    // Z must always match the implemented mux behavior.
    check_mux_function: assert property (
        @($global_clock) Z == (TE_B ? 1'b1 : A)
    );

    // When TE_B is high, Z must be forced high.
    check_te_b_high_forces_one: assert property (
        @($global_clock) TE_B |-> (Z == 1'b1)
    );

    // When TE_B is low, Z must follow A.
    check_te_b_low_follows_a: assert property (
        @($global_clock) !TE_B |-> (Z == A)
    );

    // A high Z can only occur when TE_B is high or A is high.
    check_high_output_has_valid_source: assert property (
        @($global_clock) Z |-> (TE_B || A)
    );

endmodule