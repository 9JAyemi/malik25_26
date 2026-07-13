module signal_converter_sva (
    input logic clk,
    input logic X,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic B1,
    input logic C1
);

// X must equal the RTL sum-of-products equation.
    check_x_matches_rtl_equation: assert property (
        @(posedge clk)
        X == ((A1 & A2 & A3) |
              (A1 & A2 & B1) |
              (A1 & A2 & C1) |
              (A1 & A3 & B1) |
              (A1 & A3 & C1) |
              (A1 & B1 & C1) |
              (A2 & A3 & B1) |
              (A2 & A3 & C1) |
              (A2 & B1 & C1) |
              (A3 & B1 & C1))
    );

// All three A inputs high must drive X high.
    check_all_a_high_sets_x: assert property (
        @(posedge clk)
        (A1 & A2 & A3) |-> X
    );

// A1, A2, and B1 high must drive X high.
    check_a1_a2_b1_sets_x: assert property (
        @(posedge clk)
        (A1 & A2 & B1) |-> X
    );

// A1, A2, and C1 high must drive X high.
    check_a1_a2_c1_sets_x: assert property (
        @(posedge clk)
        (A1 & A2 & C1) |-> X
    );

// A1, A3, and B1 high must drive X high.
    check_a1_a3_b1_sets_x: assert property (
        @(posedge clk)
        (A1 & A3 & B1) |-> X
    );

// A1, A3, and C1 high must drive X high.
    check_a1_a3_c1_sets_x: assert property (
        @(posedge clk)
        (A1 & A3 & C1) |-> X
    );

// A1, B1, and C1 high must drive X high.
    check_a1_b1_c1_sets_x: assert property (
        @(posedge clk)
        (A1 & B1 & C1) |-> X
    );

// A2, A3, and B1 high must drive X high.
    check_a2_a3_b1_sets_x: assert property (
        @(posedge clk)
        (A2 & A3 & B1) |-> X
    );

// A2, A3, and C1 high must drive X high.
    check_a2_a3_c1_sets_x: assert property (
        @(posedge clk)
        (A2 & A3 & C1) |-> X
    );

// A2, B1, and C1 high must drive X high.
    check_a2_b1_c1_sets_x: assert property (
        @(posedge clk)
        (A2 & B1 & C1) |-> X
    );

// A3, B1, and C1 high must drive X high.
    check_a3_b1_c1_sets_x: assert property (
        @(posedge clk)
        (A3 & B1 & C1) |-> X
    );

// If no product term is true, X must be low.
    check_no_product_term_clears_x: assert property (
        @(posedge clk)
        !((A1 & A2 & A3) |
          (A1 & A2 & B1) |
          (A1 & A2 & C1) |
          (A1 & A3 & B1) |
          (A1 & A3 & C1) |
          (A1 & B1 & C1) |
          (A2 & A3 & B1) |
          (A2 & A3 & C1) |
          (A2 & B1 & C1) |
          (A3 & B1 & C1)) |-> !X
    );

endmodule
