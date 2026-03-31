module sky130_fd_sc_hdll__or4bb_sva (
    input logic clk,
    input logic X,
    input logic A,
    input logic B,
    input logic C_N,
    input logic D_N
);

// X matches the implemented OR-of-NAND function.
    check_functional_equivalence: assert property (
        @(posedge clk) X == (A | B | ~(C_N & D_N))
    );

// A high forces X high.
    check_a_forces_x_high: assert property (
        @(posedge clk) A |-> X
    );

// B high forces X high.
    check_b_forces_x_high: assert property (
        @(posedge clk) B |-> X
    );

// C_N low with D_N low forces X high.
    check_c_n_and_d_n_low_force_x_high: assert property (
        @(posedge clk) (!C_N && !D_N) |-> X
    );

// With A and B low, X reduces to the NAND term.
    check_ab_low_reduces_to_nand_term: assert property (
        @(posedge clk) (!A && !B) |-> (X == ~(C_N & D_N))
    );

// With C_N and D_N high, X reduces to A OR B.
    check_cd_n_high_reduces_to_or: assert property (
        @(posedge clk) (C_N && D_N) |-> (X == (A | B))
    );

// A high C_N and D_N block the NAND term and force X low.
    check_cd_n_high_block_nand_term: assert property (
        @(posedge clk) (C_N && D_N) |-> (!X)
    );

// A high C_N and D_N force X low when A and B are low.
    check_cd_n_high_and_ab_low_force_x_low: assert property (
        @(posedge clk) (C_N && D_N && !A && !B) |-> (!X)
    );

// A low C_N forces X high when A and B are low.
    check_c_n_low_forces_x_high_when_ab_low: assert property (
        @(posedge clk) (!C_N && !A && !B) |-> X
    );

// A low D_N forces X high when A and B are low.
    check_d_n_low_forces_x_high_when_ab_low: assert property (
        @(posedge clk) (!D_N && !A && !B) |-> X
    );

endmodule
