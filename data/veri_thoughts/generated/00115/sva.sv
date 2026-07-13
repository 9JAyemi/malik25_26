module and_gate_assertions (
    input logic A,
    input logic B,
    input logic Y
);

    // No RTL clock or reset; sample combinational behavior on the formal global clock.

    // Output matches the AND of the inputs.
    check_and_function: assert property (
        @($global_clock) Y == (A & B)
    );

    // A high output requires A to be high.
    check_y_high_requires_a: assert property (
        @($global_clock) Y |-> A
    );

    // A high output requires B to be high.
    check_y_high_requires_b: assert property (
        @($global_clock) Y |-> B
    );

    // Both inputs high force the output high.
    check_both_high_set_y: assert property (
        @($global_clock) (A && B) |-> Y
    );

    // Any low input forces the output low.
    check_low_input_clears_y: assert property (
        @($global_clock) (!A || !B) |-> !Y
    );

endmodule