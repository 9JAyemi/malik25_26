module sky130_fd_sc_hd__a221o_sva (
    input logic clk,
    input logic X,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic B2,
    input logic C1
);

    // X matches the implemented A221O function.
    check_function_equivalence: assert property (
        @(posedge clk) X == (((A1 & A2) | (B1 & B2)) | C1)
    );

    // C1 directly drives X high through the OR stage.
    check_c1_forces_x_high: assert property (
        @(posedge clk) C1 |-> (X == 1'b1)
    );

    // A1 and A2 high drive X high through the first AND term.
    check_a_term_forces_x_high: assert property (
        @(posedge clk) (A1 & A2) |-> (X == 1'b1)
    );

    // B1 and B2 high drive X high through the second AND term.
    check_b_term_forces_x_high: assert property (
        @(posedge clk) (B1 & B2) |-> (X == 1'b1)
    );

    // If all three OR inputs are low, X must be low.
    check_all_terms_low_forces_x_low: assert property (
        @(posedge clk) (!(A1 & A2) && !(B1 & B2) && !C1) |-> (X == 1'b0)
    );

    // A low X means neither AND term nor C1 is high.
    check_x_low_means_no_active_source: assert property (
        @(posedge clk) (X == 1'b0) |-> (!(A1 & A2) && !(B1 & B2) && !C1)
    );

endmodule