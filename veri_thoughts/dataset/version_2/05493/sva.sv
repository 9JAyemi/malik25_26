module mux4to1_sva (
    input logic clk,
    input logic A0,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic [1:0] S,
    input logic X
);

    // X matches the RTL sum-of-products mux equation.
    check_mux_sum_of_products: assert property (
        @(posedge clk)
        X == ((A0 & ~S[1] & ~S[0]) |
              (A1 & ~S[1] &  S[0]) |
              (A2 &  S[1] & ~S[0]) |
              (A3 &  S[1] &  S[0]))
    );

    // When S is 00, X routes A0.
    check_sel_00_routes_a0: assert property (
        @(posedge clk) (S == 2'b00) |-> (X == A0)
    );

    // When S is 01, X routes A1.
    check_sel_01_routes_a1: assert property (
        @(posedge clk) (S == 2'b01) |-> (X == A1)
    );

    // When S is 10, X routes A2.
    check_sel_10_routes_a2: assert property (
        @(posedge clk) (S == 2'b10) |-> (X == A2)
    );

    // When S is 11, X routes A3.
    check_sel_11_routes_a3: assert property (
        @(posedge clk) (S == 2'b11) |-> (X == A3)
    );

endmodule