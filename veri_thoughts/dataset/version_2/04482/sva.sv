module mux4to1_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic C,
    input logic D,
    input logic S0,
    input logic S1,
    input logic Y
);

    // Y must match the implemented 4-to-1 mux equation.
    check_mux_equation: assert property (
        @(posedge clk)
        Y == ((A & ~S0 & ~S1) | (B & S0 & ~S1) | (C & ~S0 & S1) | (D & S0 & S1))
    );

    // Select 2'b00 routes A to Y.
    check_select_00_routes_a: assert property (
        @(posedge clk)
        (!S1 && !S0) |-> (Y == A)
    );

    // Select 2'b01 routes B to Y.
    check_select_01_routes_b: assert property (
        @(posedge clk)
        (!S1 && S0) |-> (Y == B)
    );

    // Select 2'b10 routes C to Y.
    check_select_10_routes_c: assert property (
        @(posedge clk)
        (S1 && !S0) |-> (Y == C)
    );

    // Select 2'b11 routes D to Y.
    check_select_11_routes_d: assert property (
        @(posedge clk)
        (S1 && S0) |-> (Y == D)
    );

endmodule