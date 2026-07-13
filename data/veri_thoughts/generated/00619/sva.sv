module my_module_sva (
    input logic A1,
    input logic A2,
    input logic A3,
    input logic B1,
    input logic C1,
    input logic X
);
    // No clock/reset in RTL; pure combinational. Use @($global_clock) for sampling.

    // X implements (A1|A2|A3) ^ (B1&C1).
    check_x_functional_equivalence: assert property (
        @($global_clock) X == ((A1 | A2 | A3) ^ (B1 & C1))
    );

    // If B1 or C1 is 0, X equals A1|A2|A3.
    check_bc_zero_path: assert property (
        @($global_clock) ((B1 == 1'b0) || (C1 == 1'b0)) |-> (X == (A1 | A2 | A3))
    );

    // If B1 and C1 are 1, X equals ~(A1|A2|A3).
    check_bc_one_inverts_a: assert property (
        @($global_clock) ((B1 == 1'b1) && (C1 == 1'b1)) |-> (X == ~(A1 | A2 | A3))
    );

    // If A1=A2=A3=0, X equals B1&C1.
    check_all_a_zero_path: assert property (
        @($global_clock) ((A1 == 1'b0) && (A2 == 1'b0) && (A3 == 1'b0)) |-> (X == (B1 & C1))
    );

    // If any A is 1, X equals ~(B1&C1).
    check_a_one_inverts_bc: assert property (
        @($global_clock) ((A1 | A2 | A3) == 1'b1) |-> (X == ~(B1 & C1))
    );

    // If A_out=1 and BC_out=0, X must be 1.
    check_x_one_when_a_one_bc_zero: assert property (
        @($global_clock) (((A1 | A2 | A3) == 1'b1) && ((B1 & C1) == 1'b0)) |-> (X == 1'b1)
    );

    // If A_out=0 and BC_out=1, X must be 1.
    check_x_one_when_a_zero_bc_one: assert property (
        @($global_clock) (((A1 | A2 | A3) == 1'b0) && ((B1 & C1) == 1'b1)) |-> (X == 1'b1)
    );

    // If A_out equals BC_out, X must be 0.
    check_equal_operands_yield_zero: assert property (
        @($global_clock) (((A1 | A2 | A3) == (B1 & C1))) |-> (X == 1'b0)
    );

    // If inputs are stable, X remains stable.
    check_stable_output_when_inputs_stable: assert property (
        @($global_clock) $stable({A1, A2, A3, B1, C1}) |-> $stable(X)
    );

    // X can only change when at least one input changes.
    check_no_spurious_output_toggle: assert property (
        @($global_clock) $changed(X) |-> ($changed(A1) || $changed(A2) || $changed(A3) || $changed(B1) || $changed(C1))
    );
endmodule