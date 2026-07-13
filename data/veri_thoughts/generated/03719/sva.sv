module logic_gate_sva (
    input logic A1,
    input logic A2,
    input logic B1,
    input logic C1,
    input logic X
);

    // A1 high and A2 low forces X high.
    check_a1_high_a2_low_sets_x_high: assert property (
        @($global_clock) (A1 && !A2) |-> (X == 1'b1)
    );

    // A1 low and A2 high forces X low.
    check_a1_low_a2_high_sets_x_low: assert property (
        @($global_clock) (!A1 && A2) |-> (X == 1'b0)
    );

    // With A1 and A2 both low, X equals B1 and not C1.
    check_a1_a2_low_decode: assert property (
        @($global_clock) (!A1 && !A2) |-> (X == (B1 && !C1))
    );

    // With A1 and A2 both high, X equals B1 or not C1.
    check_a1_a2_high_decode: assert property (
        @($global_clock) (A1 && A2) |-> (X == (B1 || !C1))
    );

    // X matches the complete combinational function for all input combinations.
    check_full_boolean_function: assert property (
        @($global_clock) (X == (
            (A1 && !A2) ||
            (!A1 && !A2 && B1 && !C1) ||
            (A1 && A2 && (B1 || !C1))
        ))
    );

endmodule