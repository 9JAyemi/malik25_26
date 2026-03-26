module sky130_fd_sc_ms__maj3_sva (
    input logic clk,
    input logic X,
    input logic A,
    input logic B,
    input logic C
);

    // X matches the implemented gate equation.
    check_implemented_majority_equation: assert property (
        @(posedge clk) (X == ((A & B) | ((A | B) & C)))
    );

    // A and B high force X high.
    check_ab_high_sets_x: assert property (
        @(posedge clk) ((A == 1'b1) && (B == 1'b1)) |-> (X == 1'b1)
    );

    // A and C high force X high.
    check_ac_high_sets_x: assert property (
        @(posedge clk) ((A == 1'b1) && (C == 1'b1)) |-> (X == 1'b1)
    );

    // B and C high force X high.
    check_bc_high_sets_x: assert property (
        @(posedge clk) ((B == 1'b1) && (C == 1'b1)) |-> (X == 1'b1)
    );

    // A and B low force X low.
    check_ab_low_clears_x: assert property (
        @(posedge clk) ((A == 1'b0) && (B == 1'b0)) |-> (X == 1'b0)
    );

    // A and C low force X low.
    check_ac_low_clears_x: assert property (
        @(posedge clk) ((A == 1'b0) && (C == 1'b0)) |-> (X == 1'b0)
    );

    // B and C low force X low.
    check_bc_low_clears_x: assert property (
        @(posedge clk) ((B == 1'b0) && (C == 1'b0)) |-> (X == 1'b0)
    );

endmodule