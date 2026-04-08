module my_module_sva (
    input logic Y,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic B1,
    input logic C1
);

    // Y must match the buffered NOR of B1, C1, and A1&A2&A3.
    check_y_matches_boolean_function: assert property (
        @($global_clock) Y == ~(B1 | C1 | (A3 & A1 & A2))
    );

    // B1 high forces the NOR output low.
    check_b1_high_forces_y_low: assert property (
        @($global_clock) (B1 == 1'b1) |-> (Y == 1'b0)
    );

    // C1 high forces the NOR output low.
    check_c1_high_forces_y_low: assert property (
        @($global_clock) (C1 == 1'b1) |-> (Y == 1'b0)
    );

    // All three A inputs high force the NOR output low.
    check_all_a_high_force_y_low: assert property (
        @($global_clock) ((A1 == 1'b1) && (A2 == 1'b1) && (A3 == 1'b1)) |-> (Y == 1'b0)
    );

    // With B1 and C1 low, any low A input makes Y high.
    check_any_low_a_with_low_b1_c1_forces_y_high: assert property (
        @($global_clock)
        ((B1 == 1'b0) && (C1 == 1'b0) &&
         ((A1 == 1'b0) || (A2 == 1'b0) || (A3 == 1'b0))) |-> (Y == 1'b1)
    );

    // Y high means all NOR inputs are low.
    check_y_high_requires_all_nor_inputs_low: assert property (
        @($global_clock)
        (Y == 1'b1) |-> ((B1 == 1'b0) && (C1 == 1'b0) &&
                         ((A1 == 1'b0) || (A2 == 1'b0) || (A3 == 1'b0)))
    );

    // With B1 and C1 low, Y low requires all A inputs high.
    check_y_low_with_low_b1_c1_requires_all_a_high: assert property (
        @($global_clock)
        ((B1 == 1'b0) && (C1 == 1'b0) && (Y == 1'b0)) |->
        ((A1 == 1'b1) && (A2 == 1'b1) && (A3 == 1'b1))
    );

endmodule