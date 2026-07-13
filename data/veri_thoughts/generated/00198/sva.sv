module sky130_fd_sc_ls__a221o_sva (
    input logic clk,
    input logic X,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic B2,
    input logic C1
);

    // X equals the implemented OR-of-ANDs function.
    check_output_equation: assert property (
        @(posedge clk) X == ((A1 & A2) | (B1 & B2) | C1)
    );

    // C1 high forces X high.
    check_c1_forces_high: assert property (
        @(posedge clk) C1 |-> X
    );

    // A1 and A2 high together force X high.
    check_a_pair_forces_high: assert property (
        @(posedge clk) (A1 & A2) |-> X
    );

    // B1 and B2 high together force X high.
    check_b_pair_forces_high: assert property (
        @(posedge clk) (B1 & B2) |-> X
    );

    // With no asserted term, X must be low.
    check_no_active_term_means_low: assert property (
        @(posedge clk) (!C1 && !(A1 & A2) && !(B1 & B2)) |-> !X
    );

    // A high X must come from C1 or one complete input pair.
    check_high_output_has_valid_cause: assert property (
        @(posedge clk) X |-> (C1 || (A1 & A2) || (B1 & B2))
    );

endmodule