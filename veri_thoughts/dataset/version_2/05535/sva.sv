module sky130_fd_sc_hs__a221o_sva (
    input logic A1,
    input logic A2,
    input logic B1,
    input logic B2,
    input logic C1,
    input logic X
);

    // X must always match the implemented mux expression.
    check_x_matches_implemented_mux: assert property (
        @($global_clock) X == (A1 ? B1 : C1)
    );

    // When A1 is high, X must pass B1.
    check_select_high_drives_b1: assert property (
        @($global_clock) A1 |-> (X == B1)
    );

    // When A1 is low, X must pass C1.
    check_select_low_drives_c1: assert property (
        @($global_clock) !A1 |-> (X == C1)
    );

    // If B1 and C1 are equal, X must equal that shared value.
    check_equal_data_inputs_pass_through: assert property (
        @($global_clock) (B1 == C1) |-> (X == B1)
    );

endmodule