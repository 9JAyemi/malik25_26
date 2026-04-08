module nor3_module_sva (
    input logic A,
    input logic B,
    input logic C_N,
    input logic Y
);

    // Y must always implement the RTL NOR function.
    check_y_matches_nor: assert property (
        @($global_clock) (Y == ~(A | B | C_N))
    );

    // All three low inputs must drive Y high.
    check_all_low_drives_y_high: assert property (
        @($global_clock) ((A == 1'b0) && (B == 1'b0) && (C_N == 1'b0)) |-> (Y == 1'b1)
    );

    // A high must force Y low.
    check_a_high_drives_y_low: assert property (
        @($global_clock) (A == 1'b1) |-> (Y == 1'b0)
    );

    // B high must force Y low.
    check_b_high_drives_y_low: assert property (
        @($global_clock) (B == 1'b1) |-> (Y == 1'b0)
    );

    // C_N high must force Y low.
    check_c_n_high_drives_y_low: assert property (
        @($global_clock) (C_N == 1'b1) |-> (Y == 1'b0)
    );

    // Y high means all inputs are low.
    check_y_high_means_all_inputs_low: assert property (
        @($global_clock) (Y == 1'b1) |-> ((A == 1'b0) && (B == 1'b0) && (C_N == 1'b0))
    );

    // Y low means at least one input is high.
    check_y_low_means_an_input_high: assert property (
        @($global_clock) (Y == 1'b0) |-> ((A == 1'b1) || (B == 1'b1) || (C_N == 1'b1))
    );

endmodule