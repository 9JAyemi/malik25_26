module two_to_one_mux_sva (
    input logic clk,
    input logic A1_N,
    input logic A2_N,
    input logic B1,
    input logic B2,
    input logic Y
);

    // A1_N=0 and A2_N=0 routes B1 to Y.
    check_case_00_routes_b1: assert property (
        @(posedge clk) ((A1_N == 1'b0) && (A2_N == 1'b0)) |-> (Y == B1)
    );

    // A1_N=0 and A2_N=1 routes B2 to Y.
    check_case_01_routes_b2: assert property (
        @(posedge clk) ((A1_N == 1'b0) && (A2_N == 1'b1)) |-> (Y == B2)
    );

    // A1_N=1 and A2_N=0 routes B1 to Y.
    check_case_10_routes_b1: assert property (
        @(posedge clk) ((A1_N == 1'b1) && (A2_N == 1'b0)) |-> (Y == B1)
    );

    // A1_N=1 and A2_N=1 routes B2 to Y.
    check_case_11_routes_b2: assert property (
        @(posedge clk) ((A1_N == 1'b1) && (A2_N == 1'b1)) |-> (Y == B2)
    );

    // With A2_N low, changing A1_N alone does not change Y.
    check_a1_irrelevant_when_a2_low: assert property (
        @(posedge clk) ($stable(A2_N) && (A2_N == 1'b0) && $changed(A1_N) && $stable(B1)) |-> $stable(Y)
    );

    // With A2_N high, changing A1_N alone does not change Y.
    check_a1_irrelevant_when_a2_high: assert property (
        @(posedge clk) ($stable(A2_N) && (A2_N == 1'b1) && $changed(A1_N) && $stable(B2)) |-> $stable(Y)
    );

endmodule