module binary_adder_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic CI,
    input logic SUM,
    input logic COUT_N,
    input logic VPB,
    input logic VPWR,
    input logic VGND,
    input logic VNB
);

    // SUM matches the three-input XOR.
    check_sum_equation: assert property (
        @(posedge clk) SUM == (A ^ B ^ CI)
    );

    // COUT_N is the inverted full-adder carry.
    check_cout_n_equation: assert property (
        @(posedge clk) COUT_N == ~((A & B) | ((A ^ B) & CI))
    );

    // Outputs match the 2-bit arithmetic sum.
    check_full_adder_result: assert property (
        @(posedge clk) {~COUT_N, SUM} == ({1'b0, A} + {1'b0, B} + {1'b0, CI})
    );

    // With CI low, the block behaves as a half adder.
    check_half_adder_mode: assert property (
        @(posedge clk) !CI |-> (SUM == (A ^ B)) && (COUT_N == ~(A & B))
    );

    // With CI high, SUM inverts A^B and carry becomes A|B.
    check_carry_in_high_mode: assert property (
        @(posedge clk) CI |-> (SUM == ~(A ^ B)) && (COUT_N == ~(A | B))
    );

    // Zero inputs produce zero sum and no carry.
    check_zero_case: assert property (
        @(posedge clk) (!A && !B && !CI) |-> (!SUM && COUT_N)
    );

    // All-one inputs produce sum one with carry asserted.
    check_all_one_case: assert property (
        @(posedge clk) (A && B && CI) |-> (SUM && !COUT_N)
    );

    // Exactly one high input produces sum one and no carry.
    check_one_hot_case: assert property (
        @(posedge clk) (({1'b0, A} + {1'b0, B} + {1'b0, CI}) == 2'd1) |-> (SUM && COUT_N)
    );

    // Exactly two high inputs produce zero sum with carry asserted.
    check_two_hot_case: assert property (
        @(posedge clk) (({1'b0, A} + {1'b0, B} + {1'b0, CI}) == 2'd2) |-> (!SUM && !COUT_N)
    );

endmodule