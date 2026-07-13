module mux2to1_sva (
    input logic clk,
    input logic A1_N,
    input logic A2_N,
    input logic B1,
    input logic B2,
    input logic Y
);

    // Y must match the implemented sum-of-products equation.
    check_output_equation: assert property (
        @(posedge clk)
        Y == ((~A1_N & ~A2_N & B2) |
              (~A1_N &  A2_N & B1) |
              ( A1_N & ~A2_N & B2) |
              ( A1_N &  A2_N & B1))
    );

    // All low select inputs must drive Y high.
    check_all_select_low_drives_high: assert property (
        @(posedge clk)
        (~A1_N & ~A2_N) |-> Y
    );

    // All high select inputs must drive Y high.
    check_all_select_high_drives_high: assert property (
        @(posedge clk)
        ( A1_N &  A2_N) |-> Y
    );

    // Any mixed select input combination must drive Y low.
    check_mixed_select_drives_low: assert property (
        @(posedge clk)
        ((~A1_N &  A2_N) | ( A1_N & ~A2_N)) |-> ~Y
    );

    // A high Y must come from at least one high select input combination.
    check_high_output_has_valid_select: assert property (
        @(posedge clk)
        Y |-> ((~A1_N & ~A2_N) | ( A1_N &  A2_N))
    );

    // A low Y must come from at least one mixed select input combination.
    check_low_output_has_valid_select: assert property (
        @(posedge clk)
        ~Y |-> ((~A1_N &  A2_N) | ( A1_N & ~A2_N))
    );

endmodule