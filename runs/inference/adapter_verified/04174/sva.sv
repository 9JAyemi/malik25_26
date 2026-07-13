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

// X must match the implemented combinational function.
    check_functional_equivalence: assert property (
        @(posedge clk)
        X == ((A0 & ~S0 & ~S1) | (A1 & S0 & ~S1) | (A2 & ~S0 & S1) | (A3 & S0 & S1))
    );

// When S1 is low, X must select between A0 and A1 based on S0.
    check_select_low: assert property (
        @(posedge clk)
        !S1 |-> (X == ((A0 & ~S0) | (A1 & S0)))
    );

// When S1 is high, X must select between A2 and A3 based on S0.
    check_select_high: assert property (
        @(posedge clk)
        S1 |-> (X == ((A2 & ~S0) | (A3 & S0)))
    );

// With S1 low and S0 low, X must follow A0.
    check_select_low_low: assert property (
        @(posedge clk)
        (!S1 && !S0) |-> (X == A0)
    );

// With S1 low and S0 high, X must follow A1.
    check_select_low_high: assert property (
        @(posedge clk)
        (!S1 && S0) |-> (X == A1)
    );

// With S1 high and S0 low, X must follow A2.
    check_select_high_low: assert property (
        @(posedge clk)
        (S1 && !S0) |-> (X == A2)
    );

// With S1 high and S0 high, X must follow A3.
    check_select_high_high: assert property (
        @(posedge clk)
        (S1 && S0) |-> (X == A3)
    );

endmodule
