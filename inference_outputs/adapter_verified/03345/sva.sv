module sky130_fd_sc_hvl__a21oi_sva (
    input logic clk,
    input logic Y,
    input logic A1,
    input logic A2,
    input logic B1
);

// Y matches the implemented NOR(OR(A1,A2),B1) function.
    check_function_equivalence: assert property (
        @(posedge clk) Y == ~((A1 | A2) | B1)
    );

// B1 high forces Y low.
    check_b1_forces_low: assert property (
        @(posedge clk) B1 |-> !Y
    );

// A1 and A2 high together force Y low.
    check_a1_a2_high_force_low: assert property (
        @(posedge clk) (A1 && A2) |-> !Y
    );

// With B1 low, Y follows A1|A2.
    check_b1_low_follows_or: assert property (
        @(posedge clk) !B1 |-> (Y == ~(A1 | A2))
    );

// With B1 low and A1 low, Y follows A2.
    check_b1_low_a1_low_follows_a2: assert property (
        @(posedge clk) (!B1 && !A1) |-> (Y == ~A2)
    );

// With B1 low and A2 low, Y follows A1.
    check_b1_low_a2_low_follows_a1: assert property (
        @(posedge clk) (!B1 && !A2) |-> (Y == ~A1)
    );

// A low Y requires B1 high or A1 and A2 high.
    check_low_output_has_cause: assert property (
        @(posedge clk) !Y |-> (B1 || (A1 && A2))
    );

// B1 high and A1 low force Y high.
    check_b1_high_a1_low_forces_high: assert property (
        @(posedge clk) (B1 && !A1) |-> Y
    );

// B1 high and A2 low force Y high.
    check_b1_high_a2_low_forces_high: assert property (
        @(posedge clk) (B1 && !A2) |-> Y
    );

// With B1 low and A1 high, Y is high.
    check_b1_low_a1_high_forces_high: assert property (
        @(posedge clk) (!B1 && A1) |-> Y
    );

// With B1 low and A2 high, Y is high.
    check_b1_low_a2_high_forces_high: assert property (
        @(posedge clk) (!B1 && A2) |-> Y
    );

endmodule
