module my_module_sva (
    input logic Y,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic B1
);

    // Y must equal the NOR of B1 and the 3-input AND of A1/A2/A3.
    check_output_function: assert property (
        @($global_clock) disable iff (1'b0)
        Y == ~((A1 & A2 & A3) | B1)
    );

    // B1 high forces the NOR output low.
    check_b1_forces_y_low: assert property (
        @($global_clock) disable iff (1'b0)
        B1 |-> !Y
    );

    // All three A inputs high force the AND term high and Y low.
    check_all_a_high_forces_y_low: assert property (
        @($global_clock) disable iff (1'b0)
        (A1 & A2 & A3) |-> !Y
    );

    // With B1 low, A1 low keeps the AND term low and Y high.
    check_a1_low_with_b1_low_forces_y_high: assert property (
        @($global_clock) disable iff (1'b0)
        ((!B1) & (!A1)) |-> Y
    );

    // With B1 low, A2 low keeps the AND term low and Y high.
    check_a2_low_with_b1_low_forces_y_high: assert property (
        @($global_clock) disable iff (1'b0)
        ((!B1) & (!A2)) |-> Y
    );

    // With B1 low, A3 low keeps the AND term low and Y high.
    check_a3_low_with_b1_low_forces_y_high: assert property (
        @($global_clock) disable iff (1'b0)
        ((!B1) & (!A3)) |-> Y
    );

    // Y high implies B1 is low.
    check_y_high_implies_b1_low: assert property (
        @($global_clock) disable iff (1'b0)
        Y |-> !B1
    );

    // Y high implies the 3-input AND term is low.
    check_y_high_implies_not_all_a_high: assert property (
        @($global_clock) disable iff (1'b0)
        Y |-> !(A1 & A2 & A3)
    );

    // Y low must be caused by B1 high or all A inputs high.
    check_y_low_has_valid_cause: assert property (
        @($global_clock) disable iff (1'b0)
        (!Y) |-> (B1 | (A1 & A2 & A3))
    );

    // If B1 is low and Y is low, all A inputs must be high.
    check_b1_low_and_y_low_implies_all_a_high: assert property (
        @($global_clock) disable iff (1'b0)
        ((!B1) & (!Y)) |-> (A1 & A2 & A3)
    );

endmodule