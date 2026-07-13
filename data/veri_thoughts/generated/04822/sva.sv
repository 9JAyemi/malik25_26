module sky130_fd_sc_lp__nor4_m_sva (
    input logic clk,
    input logic Y,
    input logic A,
    input logic B,
    input logic C,
    input logic D
);

    // Y must equal the 4-input NOR of A, B, C, and D.
    check_nor_equation: assert property (
        @(posedge clk) Y == ~(A | B | C | D)
    );

    // Y must be high when all inputs are low.
    check_all_low_gives_high: assert property (
        @(posedge clk) ((A == 1'b0) && (B == 1'b0) && (C == 1'b0) && (D == 1'b0)) |-> (Y == 1'b1)
    );

    // A high must force Y low.
    check_a_high_gives_low: assert property (
        @(posedge clk) (A == 1'b1) |-> (Y == 1'b0)
    );

    // B high must force Y low.
    check_b_high_gives_low: assert property (
        @(posedge clk) (B == 1'b1) |-> (Y == 1'b0)
    );

    // C high must force Y low.
    check_c_high_gives_low: assert property (
        @(posedge clk) (C == 1'b1) |-> (Y == 1'b0)
    );

    // D high must force Y low.
    check_d_high_gives_low: assert property (
        @(posedge clk) (D == 1'b1) |-> (Y == 1'b0)
    );

    // Y high implies every input is low.
    check_high_output_requires_all_low: assert property (
        @(posedge clk) (Y == 1'b1) |-> ((A == 1'b0) && (B == 1'b0) && (C == 1'b0) && (D == 1'b0))
    );

    // Y low implies at least one input is high.
    check_low_output_requires_some_high: assert property (
        @(posedge clk) (Y == 1'b0) |-> ((A == 1'b1) || (B == 1'b1) || (C == 1'b1) || (D == 1'b1))
    );

endmodule