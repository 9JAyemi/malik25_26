module mux4_1_sva (
    input logic X,
    input logic A0,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic S0,
    input logic S1,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB
);

    // X must match the implemented 4:1 mux equation.
    check_mux_equation: assert property (
        @($global_clock)
        X == ((S1 & S0 & A3) | (S1 & ~S0 & A2) | (~S1 & S0 & A1) | (~S1 & ~S0 & A0))
    );

    // When S1S0 is 00, X must select A0.
    check_select_a0: assert property (
        @($global_clock)
        ((S1 == 1'b0) && (S0 == 1'b0)) |-> (X == A0)
    );

    // When S1S0 is 01, X must select A1.
    check_select_a1: assert property (
        @($global_clock)
        ((S1 == 1'b0) && (S0 == 1'b1)) |-> (X == A1)
    );

    // When S1S0 is 10, X must select A2.
    check_select_a2: assert property (
        @($global_clock)
        ((S1 == 1'b1) && (S0 == 1'b0)) |-> (X == A2)
    );

    // When S1S0 is 11, X must select A3.
    check_select_a3: assert property (
        @($global_clock)
        ((S1 == 1'b1) && (S0 == 1'b1)) |-> (X == A3)
    );

endmodule