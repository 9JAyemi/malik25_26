module my_module_sva (
    input logic Y,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic A4,
    input logic B1
);

    // No RTL clock or reset; assertions use the formal global clock.

    // Y matches the direct composition of my_module and o41ai_2.
    check_y_structural_function: assert property (
        @($global_clock) disable iff (1'b0)
        Y == ((((A1 & A2) & (A3 & A4)) | ~((~A3) & A4)) & (A3 & (B1 | (A1 & A2))))
    );

    // Y simplifies to A3 gated by B1 or the A1/A2 conjunction.
    check_y_simplified_function: assert property (
        @($global_clock) disable iff (1'b0)
        Y == (A3 & (B1 | (A1 & A2)))
    );

    // A low A3 forces Y low.
    check_a3_low_forces_y_low: assert property (
        @($global_clock) disable iff (1'b0)
        !A3 |-> !Y
    );

    // A3 and B1 high force Y high.
    check_a3_b1_force_y_high: assert property (
        @($global_clock) disable iff (1'b0)
        (A3 & B1) |-> Y
    );

    // A3 with A1 and A2 high forces Y high.
    check_a3_a1_a2_force_y_high: assert property (
        @($global_clock) disable iff (1'b0)
        (A3 & A1 & A2) |-> Y
    );

    // With A3 high and B1 low, Y reduces to A1 & A2.
    check_b1_low_reduces_y_to_a1_a2: assert property (
        @($global_clock) disable iff (1'b0)
        (A3 & !B1) |-> (Y == (A1 & A2))
    );

    // A high Y requires either B1 or the A1/A2 conjunction.
    check_y_requires_b1_or_a1_a2: assert property (
        @($global_clock) disable iff (1'b0)
        Y |-> (B1 | (A1 & A2))
    );

endmodule