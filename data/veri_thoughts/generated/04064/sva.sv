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

    // Y must match the RTL mux equation.
    check_output_equation: assert property (
        @(posedge clk)
        Y == ((S1 & S0 & D) | (S1 & ~S0 & C) | (~S1 & S0 & B) | (~S1 & ~S0 & A))
    );

    // Select 00 routes A to Y.
    check_select_00_routes_a: assert property (
        @(posedge clk)
        (!S1 && !S0) |-> (Y == A)
    );

    // Select 01 routes B to Y.
    check_select_01_routes_b: assert property (
        @(posedge clk)
        (!S1 && S0) |-> (Y == B)
    );

    // Select 10 routes C to Y.
    check_select_10_routes_c: assert property (
        @(posedge clk)
        (S1 && !S0) |-> (Y == C)
    );

    // Select 11 routes D to Y.
    check_select_11_routes_d: assert property (
        @(posedge clk)
        (S1 && S0) |-> (Y == D)
    );

    // Stable sampled inputs imply a stable sampled output.
    check_stable_inputs_hold_output: assert property (
        @(posedge clk)
        $stable({A, B, C, D, S0, S1}) |-> $stable(Y)
    );

endmodule