module mux4to1_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic C,
    input logic D,
    input logic X,
    input logic S0,
    input logic S1
);

    // 00 selects A.
    check_select_00_routes_a: assert property (
        @(posedge clk) ((S1 == 1'b0) && (S0 == 1'b0)) |-> (X == A)
    );

    // 01 selects B.
    check_select_01_routes_b: assert property (
        @(posedge clk) ((S1 == 1'b0) && (S0 == 1'b1)) |-> (X == B)
    );

    // 10 selects C.
    check_select_10_routes_c: assert property (
        @(posedge clk) ((S1 == 1'b1) && (S0 == 1'b0)) |-> (X == C)
    );

    // 11 selects D.
    check_select_11_routes_d: assert property (
        @(posedge clk) ((S1 == 1'b1) && (S0 == 1'b1)) |-> (X == D)
    );

endmodule