module multi_input_module_sva (
    input logic clk,
    input logic X,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic A4,
    input logic B1
);

    // X must match the implemented OR-of-products equation.
    check_x_matches_or_of_products: assert property (
        @(posedge clk)
        X == ((A1 & A2 & A3) |
              (A1 & A2 & A4) |
              (A1 & A3 & A4) |
              (A2 & A3 & A4) |
              (A1 & A2 & B1) |
              (A1 & A3 & B1) |
              (A1 & A4 & B1) |
              (A2 & A3 & B1) |
              (A2 & A4 & B1) |
              (A3 & A4 & B1))
    );

    // X must be high when any three A inputs are high.
    check_x_high_when_three_a_high: assert property (
        @(posedge clk)
        ((A1 & A2 & A3) |
         (A1 & A2 & A4) |
         (A1 & A3 & A4) |
         (A2 & A3 & A4))
        |-> X
    );

    // X must be high when any two A inputs and B1 are high.
    check_x_high_when_two_a_and_b1_high: assert property (
        @(posedge clk)
        ((A1 & A2 & B1) |
         (A1 & A3 & B1) |
         (A1 & A4 & B1) |
         (A2 & A3 & B1) |
         (A2 & A4 & B1) |
         (A3 & A4 & B1))
        |-> X
    );

    // X must be low when no term in the OR-of-products is true.
    check_x_low_when_no_term_true: assert property (
        @(posedge clk)
        !((A1 & A2 & A3) |
          (A1 & A2 & A4) |
          (A1 & A3 & A4) |
          (A2 & A3 & A4) |
          (A1 & A2 & B1) |
          (A1 & A3 & B1) |
          (A1 & A4 & B1) |
          (A2 & A3 & B1) |
          (A2 & A4 & B1) |
          (A3 & A4 & B1))
        |-> !X
    );

    // X must be low when all A inputs are low.
    check_x_low_when_all_a_low: assert property (
        @(posedge clk)
        !(A1 | A2 | A3 | A4) |-> !X
    );

    // X must be low when all B1-enabled terms are false.
    check_x_low_when_b1_enabled_terms_false: assert property (
        @(posedge clk)
        !(A1 & A2 & B1) &&
        !(A1 & A3 & B1) &&
        !(A1 & A4 & B1) &&
        !(A2 & A3 & B1) &&
        !(A2 & A4 & B1) &&
        !(A3 & A4 & B1)
        |-> !X
    );

endmodule