module sky130_fd_sc_hdll__o2bb2ai_sva (
    input logic clk,
    input logic Y,
    input logic A1_N,
    input logic A2_N,
    input logic B1,
    input logic B2
);

// Y matches the implemented NAND/OR/NAND/BUF logic.
    check_functional_equivalence: assert property (
        @(posedge clk) Y == ~(~(A1_N & A2_N) | (B1 | B2))
    );

// A high B1 forces Y low.
    check_b1_forces_low: assert property (
        @(posedge clk) B1 |-> !Y
    );

// A high B2 forces Y low.
    check_b2_forces_low: assert property (
        @(posedge clk) B2 |-> !Y
    );

// A low A1_N forces Y low.
    check_a1n_low_forces_low: assert property (
        @(posedge clk) !A1_N |-> !Y
    );

// A low A2_N forces Y low.
    check_a2n_low_forces_low: assert property (
        @(posedge clk) !A2_N |-> !Y
    );

// With all B inputs low and both A inputs high, Y is high.
    check_all_enable_high_drives_high: assert property (
        @(posedge clk) (!B1 && !B2 && A1_N && A2_N) |-> Y
    );

// A high Y requires all B inputs low and both A inputs high.
    check_high_output_requires_all_enable: assert property (
        @(posedge clk) Y |-> (!B1 && !B2 && A1_N && A2_N)
    );

endmodule
