module signal_converter_sva (
    input logic clk,
    input logic X,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic B1,
    input logic C1
);

    // X must equal the OR of all pairwise and triple product terms.
    check_x_matches_product_sum: assert property (
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

    // X must be low when no input term is fully asserted.
    check_x_low_when_no_term_true: assert property (
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

    // X must be high when A1 and A2 are high.
    check_x_high_when_a1_a2_high: assert property (
        @(posedge clk)
        (A1 & A2) |-> X
    );

    // X must be high when A1 and A3 are high.
    check_x_high_when_a1_a3_high: assert property (
        @(posedge clk)
        (A1 & A3) |-> X
    );

    // X must be high when A1 and B1 are high.
    check_x_high_when_a1_b1_high: assert property (
        @(posedge clk)
        (A1 & B1) |-> X
    );

    // X must be high when A1 and C1 are high.
    check_x_high_when_a1_c1_high: assert property (
        @(posedge clk)
        (A1 & C1) |-> X
    );

    // X must be high when A2 and A3 are high.
    check_x_high_when_a2_a3_high: assert property (
        @(posedge clk)
        (A2 & A3) |-> X
    );

    // X must be high when A2 and B1 are high.
    check_x_high_when_a2_b1_high: assert property (
        @(posedge clk)
        (A2 & B1) |-> X
    );

    // X must be high when A2 and C1 are high.
    check_x_high_when_a2_c1_high: assert property (
        @(posedge clk)
        (A2 & C1) |-> X
    );

    // X must be high when A3 and B1 are high.
    check_x_high_when_a3_b1_high: assert property (
        @(posedge clk)
        (A3 & B1) |-> X
    );

    // X must be high when A3 and C1 are high.
    check_x_high_when_a3_c1_high: assert property (
        @(posedge clk)
        (A3 & C1) |-> X
    );

endmodule