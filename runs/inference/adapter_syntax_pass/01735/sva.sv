module tri_buf_sva (
    input logic A,
    input logic Z,
    input logic TE_B
);

    // Z must always match the tri-state function.
    check_tri_state_function: assert property (
        @($global_clock) Z === ((TE_B) ? 1'b0 : A)
    );

    // When TE_B is high, Z must be driven low.
    check_te_b_high_forces_zero: assert property (
        @($global_clock) TE_B |-> (Z === 1'b0)
    );

    // When TE_B is low, Z must follow A.
    check_te_b_low_passes_a: assert property (
        @($global_clock) !TE_B |-> (Z === A)
    );

endmodule