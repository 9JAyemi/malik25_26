module sky130_fd_sc_hd__a41oi_sva (
    input logic Y,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic A4,
    input logic B1
);

    // Y implements ~(B1 | (A1 & A2 & A3 & A4)).
    check_boolean_function: assert property (
        @($global_clock) Y == ~(B1 | (A1 & A2 & A3 & A4))
    );

    // B1 high forces the NOR output low.
    check_b1_forces_low: assert property (
        @($global_clock) B1 |-> !Y
    );

    // All four A inputs high force the AND term high and Y low.
    check_all_a_high_forces_low: assert property (
        @($global_clock) (A1 & A2 & A3 & A4) |-> !Y
    );

    // With B1 low, any low A input makes Y high.
    check_b1_low_and_any_a_low_forces_high: assert property (
        @($global_clock) (!B1 && (!A1 || !A2 || !A3 || !A4)) |-> Y
    );

    // Y high requires B1 to be low.
    check_y_high_requires_b1_low: assert property (
        @($global_clock) Y |-> !B1
    );

    // Y high requires the four-input AND term to be low.
    check_y_high_requires_a_not_all_high: assert property (
        @($global_clock) Y |-> (!A1 || !A2 || !A3 || !A4)
    );

    // If Y is low while B1 is low, all A inputs must be high.
    check_y_low_with_b1_low_requires_all_a_high: assert property (
        @($global_clock) (!Y && !B1) |-> (A1 && A2 && A3 && A4)
    );

    // If Y is low while any A input is low, B1 must be high.
    check_y_low_with_any_a_low_requires_b1_high: assert property (
        @($global_clock) (!Y && (!A1 || !A2 || !A3 || !A4)) |-> B1
    );

endmodule