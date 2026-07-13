module mux4_sva (
    input logic A,
    input logic B,
    input logic C,
    input logic D,
    input logic S0,
    input logic S1,
    input logic Y
);

    // No explicit clock or reset exists in the RTL; sample on the global clock.

    // When S1S0 is 00, Y must equal A.
    check_select_00: assert property (
        @($global_clock) ({S1, S0} === 2'b00) |-> (Y === A)
    );

    // When S1S0 is 01, Y must equal B.
    check_select_01: assert property (
        @($global_clock) ({S1, S0} === 2'b01) |-> (Y === B)
    );

    // When S1S0 is 10, Y must equal C.
    check_select_10: assert property (
        @($global_clock) ({S1, S0} === 2'b10) |-> (Y === C)
    );

    // When S1S0 is 11, Y must equal D.
    check_select_11: assert property (
        @($global_clock) ({S1, S0} === 2'b11) |-> (Y === D)
    );

endmodule