module sky130_fd_sc_lp__a21boi_sva (
    input logic clk,
    input logic Y,
    input logic A1,
    input logic A2,
    input logic B1_N
);

// Y matches the implemented NOR/NOT/AND logic.
    check_functional_equivalence: assert property (
        @(posedge clk) Y == ~((~B1_N) | (A1 & A2))
    );

// A high B1_N forces Y high.
    check_b1n_high_forces_y_high: assert property (
        @(posedge clk) (B1_N == 1'b1) |-> (Y == 1'b1)
    );

// A low B1_N forces Y low.
    check_b1n_low_forces_y_low: assert property (
        @(posedge clk) (B1_N == 1'b0) |-> (Y == 1'b0)
    );

// A high A1 and A2 force Y low.
    check_a1_a2_high_force_y_low: assert property (
        @(posedge clk) ((A1 == 1'b1) && (A2 == 1'b1)) |-> (Y == 1'b0)
    );

// A low A1 with B1_N high forces Y high.
    check_a1_low_with_b1n_high_forces_y_high: assert property (
        @(posedge clk) ((A1 == 1'b0) && (B1_N == 1'b1)) |-> (Y == 1'b1)
    );

// A low A2 with B1_N high forces Y high.
    check_a2_low_with_b1n_high_forces_y_high: assert property (
        @(posedge clk) ((A2 == 1'b0) && (B1_N == 1'b1)) |-> (Y == 1'b1)
    );

// A low A1 and B1_N low forces Y low.
    check_a1_low_with_b1n_low_forces_y_low: assert property (
        @(posedge clk) ((A1 == 1'b0) && (B1_N == 1'b0)) |-> (Y == 1'b0)
    );

// A low A2 and B1_N low forces Y low.
    check_a2_low_with_b1n_low_forces_y_low: assert property (
        @(posedge clk) ((A2 == 1'b0) && (B1_N == 1'b0)) |-> (Y == 1'b0)
    );

endmodule
