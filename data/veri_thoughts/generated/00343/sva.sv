module sky130_fd_sc_ls__fahcon_sva (
    input logic clk,
    input logic COUT_N,
    input logic SUM,
    input logic A,
    input logic B,
    input logic CI
);

    // SUM must be the XOR of the three inputs.
    check_sum_xor_function: assert property (
        @(posedge clk) SUM == (A ^ B ^ CI)
    );

    // COUT_N must match the implemented NOR/OR carry network.
    check_coutn_gate_function: assert property (
        @(posedge clk) COUT_N == ((~(A | B)) | (~(A | CI)) | (~(B | CI)))
    );

    // The outputs must encode the 2-bit result of A+B+CI.
    check_full_adder_result: assert property (
        @(posedge clk) ({1'b0, A} + {1'b0, B} + {1'b0, CI}) == {~COUT_N, SUM}
    );

    // 000 must produce SUM=0 and COUT_N=1.
    check_all_zero_case: assert property (
        @(posedge clk) (!A && !B && !CI) |-> ((SUM == 1'b0) && (COUT_N == 1'b1))
    );

    // 001 must produce SUM=1 and COUT_N=1.
    check_ci_only_case: assert property (
        @(posedge clk) (!A && !B && CI) |-> ((SUM == 1'b1) && (COUT_N == 1'b1))
    );

    // 010 must produce SUM=1 and COUT_N=1.
    check_b_only_case: assert property (
        @(posedge clk) (!A && B && !CI) |-> ((SUM == 1'b1) && (COUT_N == 1'b1))
    );

    // 011 must produce SUM=0 and COUT_N=0.
    check_b_ci_case: assert property (
        @(posedge clk) (!A && B && CI) |-> ((SUM == 1'b0) && (COUT_N == 1'b0))
    );

    // 100 must produce SUM=1 and COUT_N=1.
    check_a_only_case: assert property (
        @(posedge clk) (A && !B && !CI) |-> ((SUM == 1'b1) && (COUT_N == 1'b1))
    );

    // 101 must produce SUM=0 and COUT_N=0.
    check_a_ci_case: assert property (
        @(posedge clk) (A && !B && CI) |-> ((SUM == 1'b0) && (COUT_N == 1'b0))
    );

    // 110 must produce SUM=0 and COUT_N=0.
    check_a_b_case: assert property (
        @(posedge clk) (A && B && !CI) |-> ((SUM == 1'b0) && (COUT_N == 1'b0))
    );

    // 111 must produce SUM=1 and COUT_N=0.
    check_all_one_case: assert property (
        @(posedge clk) (A && B && CI) |-> ((SUM == 1'b1) && (COUT_N == 1'b0))
    );

endmodule