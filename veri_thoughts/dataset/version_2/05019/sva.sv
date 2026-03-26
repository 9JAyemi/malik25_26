module sky130_fd_sc_hd__a221oi_sva (
    input logic Y,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic B2,
    input logic C1
);

    // No RTL clock or reset; sample this combinational cell on the formal global clock.

    // Y matches the implemented NOR/AND logic equation.
    check_output_equation: assert property (
        @($global_clock)
        Y == ~(((B1 & B2) | C1 | (A1 & A2)))
    );

    // C1 high forces the output low.
    check_c1_forces_low: assert property (
        @($global_clock)
        C1 |-> (Y == 1'b0)
    );

    // A1 and A2 high together force the output low.
    check_a_pair_forces_low: assert property (
        @($global_clock)
        (A1 & A2) |-> (Y == 1'b0)
    );

    // B1 and B2 high together force the output low.
    check_b_pair_forces_low: assert property (
        @($global_clock)
        (B1 & B2) |-> (Y == 1'b0)
    );

    // With no active NOR input term, the output is high.
    check_no_active_term_drives_high: assert property (
        @($global_clock)
        (!(B1 & B2) && !C1 && !(A1 & A2)) |-> (Y == 1'b1)
    );

    // A high output means none of the three NOR inputs is asserted.
    check_y_high_requires_no_active_term: assert property (
        @($global_clock)
        Y |-> (!(B1 & B2) && !C1 && !(A1 & A2))
    );

    // A low output means at least one NOR input term is asserted.
    check_y_low_requires_active_term: assert property (
        @($global_clock)
        !Y |-> ((B1 & B2) || C1 || (A1 & A2))
    );

endmodule