module MUX4X1_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic C,
    input logic D,
    input logic S0,
    input logic S1,
    input logic Y
);

    // Y matches the implemented 4:1 mux equation.
    check_mux_equation: assert property (
        @(posedge clk)
        Y == ((A && !S1 && !S0) ||
              (B && !S1 &&  S0) ||
              (C &&  S1 && !S0) ||
              (D &&  S1 &&  S0))
    );

    // When S1S0 is 00, Y follows A.
    check_select_00_routes_a: assert property (
        @(posedge clk)
        (!S1 && !S0) |-> (Y == A)
    );

    // When S1S0 is 01, Y follows B.
    check_select_01_routes_b: assert property (
        @(posedge clk)
        (!S1 && S0) |-> (Y == B)
    );

    // When S1S0 is 10, Y follows C.
    check_select_10_routes_c: assert property (
        @(posedge clk)
        (S1 && !S0) |-> (Y == C)
    );

    // When S1S0 is 11, Y follows D.
    check_select_11_routes_d: assert property (
        @(posedge clk)
        (S1 && S0) |-> (Y == D)
    );

endmodule