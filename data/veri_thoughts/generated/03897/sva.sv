module mux_4to1_sva(
    input logic A,
    input logic B,
    input logic C,
    input logic D,
    input logic S0,
    input logic S1,
    input logic Y
);

    // No RTL clock or reset; sample on the formal global clock.

    // When select is 00, output matches A.
    check_select_00: assert property (
        @($global_clock) ((S1 === 1'b0) && (S0 === 1'b0)) |-> (Y === A)
    );

    // When select is 01, output matches B.
    check_select_01: assert property (
        @($global_clock) ((S1 === 1'b0) && (S0 === 1'b1)) |-> (Y === B)
    );

    // When select is 10, output matches C.
    check_select_10: assert property (
        @($global_clock) ((S1 === 1'b1) && (S0 === 1'b0)) |-> (Y === C)
    );

    // When select is 11, output matches D.
    check_select_11: assert property (
        @($global_clock) ((S1 === 1'b1) && (S0 === 1'b1)) |-> (Y === D)
    );

    // Output matches the implemented 4-to-1 mux equation.
    check_mux_equation: assert property (
        @($global_clock) Y === ((A & ~S1 & ~S0) | (B & ~S1 & S0) | (C & S1 & ~S0) | (D & S1 & S0))
    );

endmodule