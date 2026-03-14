module sky130_fd_sc_lp__fahcon_sva (
    input logic COUT_N,
    input logic SUM,
    input logic A,
    input logic B,
    input logic CI
);
    // Combinational cell with no clock/reset; sample on input edges.

    // SUM equals three-input XOR (sampled on A edge).
    sum_eq_xor_on_A: assert property (
        @(posedge A) SUM == (A ^ B ^ CI)
    );

    // SUM equals three-input XOR (sampled on B edge).
    sum_eq_xor_on_B: assert property (
        @(posedge B) SUM == (A ^ B ^ CI)
    );

    // SUM equals three-input XOR (sampled on CI edge).
    sum_eq_xor_on_CI: assert property (
        @(posedge CI) SUM == (A ^ B ^ CI)
    );

    // COUT_N equals OR of NOR terms per RTL (sampled on A edge).
    coutn_eq_or_nor_on_A: assert property (
        @(posedge A) COUT_N == ((~(A|B)) | (~(A|CI)) | (~(B|CI)))
    );

    // COUT_N equals OR of NOR terms per RTL (sampled on B edge).
    coutn_eq_or_nor_on_B: assert property (
        @(posedge B) COUT_N == ((~(A|B)) | (~(A|CI)) | (~(B|CI)))
    );

    // COUT_N equals OR of NOR terms per RTL (sampled on CI edge).
    coutn_eq_or_nor_on_CI: assert property (
        @(posedge CI) COUT_N == ((~(A|B)) | (~(A|CI)) | (~(B|CI)))
    );

    // If A and B are 1, COUT_N must be 0 regardless of CI.
    coutn_zero_when_A_and_B_one: assert property (
        @(posedge A) (A && B) |-> (COUT_N == 1'b0)
    );

    // If A and CI are 1, COUT_N must be 0 regardless of B.
    coutn_zero_when_A_and_CI_one: assert property (
        @(posedge CI) (A && CI) |-> (COUT_N == 1'b0)
    );

    // If B and CI are 1, COUT_N must be 0 regardless of A.
    coutn_zero_when_B_and_CI_one: assert property (
        @(posedge B) (B && CI) |-> (COUT_N == 1'b0)
    );

    // When A and B are equal, SUM equals CI.
    sum_equals_CI_when_A_eq_B: assert property (
        @(posedge CI) (A == B) |-> (SUM == CI)
    );
endmodule