module my_circuit_sva (
    input logic X,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic A4,
    input logic B1
);

    // No RTL clock or reset; sample the combinational logic on the formal global clock.

    // X must always match the RTL mux expression.
    check_x_matches_rtl: assert property (
        @($global_clock)
        (X == ((A1) ? 1'b1 : (A2) ? 1'b0 : (A3) ? ~A4 : (B1) ? 1'b0 : 1'b0))
    );

    // A1 has highest priority and forces X high.
    check_a1_priority: assert property (
        @($global_clock)
        A1 |-> (X == 1'b1)
    );

    // A2 forces X low when A1 is low.
    check_a2_priority: assert property (
        @($global_clock)
        (!A1 && A2) |-> (X == 1'b0)
    );

    // A3 selects the inverted A4 value when A1 and A2 are low.
    check_a3_inverts_a4: assert property (
        @($global_clock)
        (!A1 && !A2 && A3) |-> (X == ~A4)
    );

    // With A1, A2, and A3 low, X is low regardless of B1.
    check_default_low: assert property (
        @($global_clock)
        (!A1 && !A2 && !A3) |-> (X == 1'b0)
    );

endmodule