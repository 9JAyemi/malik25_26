module sky130_fd_sc_hd__a22o_sva (
    input logic clk,
    input logic X,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic B2
);
    // X equals (A1 & A2) | (B1 & B2).
    check_x_function_equivalence: assert property (
        @(posedge clk) X == ((A1 && A2) || (B1 && B2))
    );

    // If X is HIGH, at least one pair (A1&A2 or B1&B2) is HIGH.
    check_x_high_implies_pair: assert property (
        @(posedge clk) X |-> ((A1 && A2) || (B1 && B2))
    );

    // If A1&A2 is HIGH, X must be HIGH.
    check_a_pair_drives_x: assert property (
        @(posedge clk) (A1 && A2) |-> (X == 1'b1)
    );

    // If B1&B2 is HIGH, X must be HIGH.
    check_b_pair_drives_x: assert property (
        @(posedge clk) (B1 && B2) |-> (X == 1'b1)
    );

    // If both pairs are LOW, X must be LOW.
    check_both_pairs_low_force_x_low: assert property (
        @(posedge clk) (!(A1 && A2) && !(B1 && B2)) |-> (X == 1'b0)
    );

    // If A1 and B1 are LOW, X must be LOW.
    check_low_a1_b1_force_x_low: assert property (
        @(posedge clk) (!A1 && !B1) |-> (X == 1'b0)
    );

    // If A2 and B2 are LOW, X must be LOW.
    check_low_a2_b2_force_x_low: assert property (
        @(posedge clk) (!A2 && !B2) |-> (X == 1'b0)
    );

    // On a rising edge of X, at least one pair must be HIGH that cycle.
    check_rose_x_requires_pair_high: assert property (
        @(posedge clk) $rose(X) |-> ((A1 && A2) || (B1 && B2))
    );

    // On a falling edge of X, both pairs must be LOW that cycle.
    check_fell_x_requires_pairs_low: assert property (
        @(posedge clk) $fell(X) |-> (!(A1 && A2) && !(B1 && B2))
    );

    // If inputs are stable across cycles, X must be stable.
    check_stable_inputs_imply_stable_x: assert property (
        @(posedge clk) $stable({A1, A2, B1, B2}) |-> $stable(X)
    );
endmodule