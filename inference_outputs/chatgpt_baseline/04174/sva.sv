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

    // X must match the full mux sum-of-products equation.
    check_output_equation: assert property (
        @(posedge clk) disable iff (1'b0)
        X == ((A0 & ~S0 & ~S1) |
              (A1 &  S0 & ~S1) |
              (A2 & ~S0 &  S1) |
              (A3 &  S0 &  S1))
    );

    // When select is 00, X must follow A0.
    check_select_00: assert property (
        @(posedge clk) disable iff (1'b0)
        ((S1 == 1'b0) && (S0 == 1'b0)) |-> (X == A0)
    );

    // When select is 01, X must follow A1.
    check_select_01: assert property (
        @(posedge clk) disable iff (1'b0)
        ((S1 == 1'b0) && (S0 == 1'b1)) |-> (X == A1)
    );

    // When select is 10, X must follow A2.
    check_select_10: assert property (
        @(posedge clk) disable iff (1'b0)
        ((S1 == 1'b1) && (S0 == 1'b0)) |-> (X == A2)
    );

    // When select is 11, X must follow A3.
    check_select_11: assert property (
        @(posedge clk) disable iff (1'b0)
        ((S1 == 1'b1) && (S0 == 1'b1)) |-> (X == A3)
    );

    // With S1 low, X must select between A0 and A1 using S0.
    check_s1_low_lower_pair: assert property (
        @(posedge clk) disable iff (1'b0)
        (S1 == 1'b0) |-> (X == ((A0 & ~S0) | (A1 & S0)))
    );

    // With S1 high, X must select between A2 and A3 using S0.
    check_s1_high_upper_pair: assert property (
        @(posedge clk) disable iff (1'b0)
        (S1 == 1'b1) |-> (X == ((A2 & ~S0) | (A3 & S0)))
    );

    // With S0 low, X must select between A0 and A2 using S1.
    check_s0_low_even_pair: assert property (
        @(posedge clk) disable iff (1'b0)
        (S0 == 1'b0) |-> (X == ((A0 & ~S1) | (A2 & S1)))
    );

    // With S0 high, X must select between A1 and A3 using S1.
    check_s0_high_odd_pair: assert property (
        @(posedge clk) disable iff (1'b0)
        (S0 == 1'b1) |-> (X == ((A1 & ~S1) | (A3 & S1)))
    );

endmodule