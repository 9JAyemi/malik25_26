module sky130_fd_sc_ls__a221o_sva (
    input logic clk,
    input logic X,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic B2,
    input logic C1
);

    // X must match the implemented AO221 logic function.
    check_full_function: assert property (
        @(posedge clk) X === (((A1 & A2) | (B1 & B2)) | C1)
    );

    // The A1/A2 product term must drive X high.
    check_a_term_drives_high: assert property (
        @(posedge clk) (A1 & A2) |-> X
    );

    // The B1/B2 product term must drive X high.
    check_b_term_drives_high: assert property (
        @(posedge clk) (B1 & B2) |-> X
    );

    // C1 must drive X high through the OR stage.
    check_c1_drives_high: assert property (
        @(posedge clk) C1 |-> X
    );

    // If all three OR inputs are low, X must be low.
    check_no_term_drives_low: assert property (
        @(posedge clk) !(((A1 & A2) | (B1 & B2)) | C1) |-> !X
    );

    // A low X means the A1/A2 product term is not asserted.
    check_x_low_implies_a_term_low: assert property (
        @(posedge clk) !X |-> !(A1 & A2)
    );

    // A low X means the B1/B2 product term is not asserted.
    check_x_low_implies_b_term_low: assert property (
        @(posedge clk) !X |-> !(B1 & B2)
    );

    // A low X means C1 is not asserted.
    check_x_low_implies_c1_low: assert property (
        @(posedge clk) !X |-> !C1
    );

endmodule