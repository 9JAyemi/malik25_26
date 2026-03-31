module sky130_fd_sc_lp__a21oi_sva (
    input logic clk,
    input logic Y,
    input logic A1,
    input logic A2,
    input logic B1
);

// Y matches the implemented NOR(AND(A1,A2), B1) function.
    check_functional_equivalence: assert property (
        @(posedge clk) Y == ~((A1 & A2) | B1)
    );

// B1 high forces Y low.
    check_b1_forces_y_low: assert property (
        @(posedge clk) B1 |-> !Y
    );

// A1 and A2 high together force Y low.
    check_a1_a2_high_force_y_low: assert property (
        @(posedge clk) (A1 && A2) |-> !Y
    );

// With B1 low, Y equals the inverted AND of A1 and A2.
    check_b1_low_y_equals_not_a1_a2: assert property (
        @(posedge clk) !B1 |-> (Y == ~(A1 & A2))
    );

// With A1 and A2 low, Y equals the inverted B1.
    check_a1_a2_low_y_equals_not_b1: assert property (
        @(posedge clk) (!A1 && !A2) |-> (Y == ~B1)
    );

// A high Y requires B1 low and at least one of A1 or A2 low.
    check_y_high_requires_b1_low_and_not_both_a1_a2: assert property (
        @(posedge clk) Y |-> (!B1 && (!A1 || !A2))
    );

// A low Y requires B1 high or both A1 and A2 high.
    check_y_low_requires_b1_high_or_both_a1_a2: assert property (
        @(posedge clk) !Y |-> (B1 || (A1 && A2))
    );

endmodule
