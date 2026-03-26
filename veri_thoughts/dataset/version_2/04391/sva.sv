module mux4to1_assertions (
    input logic clk,
    input logic Y,
    input logic A,
    input logic B,
    input logic C,
    input logic D,
    input logic S0,
    input logic S1
);

    // Y must match the RTL mux expression on every sampled cycle.
    check_mux_expression: assert property (
        @(posedge clk)
        Y == ((S1 & S0) ? D : ((S1 & ~S0) ? C : (((~S1) & S0) ? B : A)))
    );

    // Select 00 routes A to Y.
    check_select_00_routes_A: assert property (
        @(posedge clk)
        (!S1 && !S0) |-> (Y == A)
    );

    // Select 01 routes B to Y.
    check_select_01_routes_B: assert property (
        @(posedge clk)
        (!S1 && S0) |-> (Y == B)
    );

    // Select 10 routes C to Y.
    check_select_10_routes_C: assert property (
        @(posedge clk)
        (S1 && !S0) |-> (Y == C)
    );

    // Select 11 routes D to Y.
    check_select_11_routes_D: assert property (
        @(posedge clk)
        (S1 && S0) |-> (Y == D)
    );

endmodule