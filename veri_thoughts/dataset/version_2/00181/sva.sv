module sky130_fd_sc_hd__fahcon_sva (
    input logic clk,
    input logic COUT_N,
    input logic SUM,
    input logic A,
    input logic B,
    input logic CI
);

    // SUM is the three-input XOR of A, B, and CI.
    check_sum_parity: assert property (
        @(posedge clk) SUM == (A ^ B ^ CI)
    );

    // COUT_N is the inverted carry-out from the three inputs.
    check_coutn_function: assert property (
        @(posedge clk) COUT_N == ~((A & B) | (A & CI) | (B & CI))
    );

    // The outputs encode a full-adder result with active-low carry.
    check_full_adder_encoding: assert property (
        @(posedge clk) ({1'b0, A} + {1'b0, B} + {1'b0, CI}) == {~COUT_N, SUM}
    );

    // All-zero inputs produce zero sum and deasserted carry.
    check_all_zero_case: assert property (
        @(posedge clk) (!A && !B && !CI) |-> (!SUM && COUT_N)
    );

    // Any single high input produces sum one and deasserted carry.
    check_one_high_case: assert property (
        @(posedge clk)
        ((A && !B && !CI) || (!A && B && !CI) || (!A && !B && CI)) |-> (SUM && COUT_N)
    );

    // Any two high inputs produce sum zero and asserted carry.
    check_two_high_case: assert property (
        @(posedge clk)
        ((A && B && !CI) || (A && !B && CI) || (!A && B && CI)) |-> (!SUM && !COUT_N)
    );

    // All-one inputs produce sum one and asserted carry.
    check_all_one_case: assert property (
        @(posedge clk) (A && B && CI) |-> (SUM && !COUT_N)
    );

endmodule