module mux2to1_sva (
    input logic clk,
    input logic A1_N,
    input logic A2_N,
    input logic B1,
    input logic B2,
    input logic Y
);

    // Y matches the RTL sum-of-products equation.
    check_y_matches_rtl_equation: assert property (
        @(posedge clk)
        Y == ((~A1_N & ~A2_N & B1) |
              (~A1_N &  A2_N & B2) |
              ( A1_N & ~A2_N & B2) |
              ( A1_N &  A2_N & B1))
    );

    // When both select inputs are low, Y follows B1.
    check_select_00_routes_b1: assert property (
        @(posedge clk)
        (~A1_N & ~A2_N) |-> (Y == B1)
    );

    // When A1 is low and A2 is high, Y follows B2.
    check_select_01_routes_b2: assert property (
        @(posedge clk)
        (~A1_N &  A2_N) |-> (Y == B2)
    );

    // When A1 is high and A2 is low, Y follows B2.
    check_select_10_routes_b2: assert property (
        @(posedge clk)
        ( A1_N & ~A2_N) |-> (Y == B2)
    );

    // When both select inputs are high, Y follows B1.
    check_select_11_routes_b1: assert property (
        @(posedge clk)
        ( A1_N &  A2_N) |-> (Y == B1)
    );

endmodule