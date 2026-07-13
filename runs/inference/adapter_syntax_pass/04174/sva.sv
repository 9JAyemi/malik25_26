module mux4_sva (
    input logic clk,
    input logic A0,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic S0,
    input logic S1,
    input logic X
);

    // X must match the implemented mux equation.
    check_mux_equation: assert property (
        @(posedge clk)
        X == ((A0 & ~S0 & ~S1) | (A1 & S0 & ~S1) | (A2 & ~S0 & S1) | (A3 & S0 & S1))
    );

    // When S1 is low, X must select A0.
    check_select_a0: assert property (
        @(posedge clk)
        (!S1) |-> (X == A0)
    );

    // When S1 is high, X must select A3.
    check_select_a3: assert property (
        @(posedge clk)
        S1 |-> (X == A3)
    );

    // When S0 is low, X must select A2.
    check_select_a2: assert property (
        @(posedge clk)
        (!S0) |-> (X == A2)
    );

    // When S0 is high, X must select A1.
    check_select_a1: assert property (
        @(posedge clk)
        S0 |-> (X == A1)
    );

    // With S1 low and S0 low, X must be low.
    check_select_a0_low_low: assert property (
        @(posedge clk)
        (!S1 && !S0) |-> (X == 1'b0)
    );

    // With S1 low and S0 high, X must be high.
    check_select_a1_low_high: assert property (
        @(posedge clk)
        (!S1 && S0) |-> (X == 1'b1)
    );

    // With S1 high and S0 low, X must be high.
    check_select_a2_high_low: assert property (
        @(posedge clk)
        (S1 && !S0) |-> (X == 1'b1)
    );

    // With S1 high and S0 high, X must be low.
    check_select_a3_high_high: assert property (
        @(posedge clk)
        (S1 && S0) |-> (X == 1'b0)
    );

endmodule