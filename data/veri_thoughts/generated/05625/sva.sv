module sky130_fd_sc_hd__and2b_sva (
    input logic X,
    input logic A_N,
    input logic B
);

    // No clock or reset exists in the RTL; sample on Jasper's global clock.

    // X must implement the inverted-A AND B function.
    check_functional_equivalence: assert property (
        @($global_clock) X == ((~A_N) & B)
    );

    // A_N high must force X low.
    check_a_n_high_forces_zero: assert property (
        @($global_clock) (A_N == 1'b1) |-> (X == 1'b0)
    );

    // B low must force X low.
    check_b_low_forces_zero: assert property (
        @($global_clock) (B == 1'b0) |-> (X == 1'b0)
    );

    // A_N low with B high must drive X high.
    check_active_input_combination_drives_one: assert property (
        @($global_clock) ((A_N == 1'b0) && (B == 1'b1)) |-> (X == 1'b1)
    );

    // X high is only possible when A_N is low and B is high.
    check_output_high_requires_matching_inputs: assert property (
        @($global_clock) (X == 1'b1) |-> ((A_N == 1'b0) && (B == 1'b1))
    );

endmodule