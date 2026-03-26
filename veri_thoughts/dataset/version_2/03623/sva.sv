module sky130_fd_sc_hd__fah_sva (
    input logic clk,
    input logic COUT,
    input logic SUM,
    input logic A,
    input logic B,
    input logic CI
);

    // SUM is the parity of A, B, and CI.
    check_sum_matches_xor: assert property (
        @(posedge clk) disable iff (1'b0)
        SUM == (A ^ B ^ CI)
    );

    // COUT is high when at least two inputs are high.
    check_cout_matches_majority: assert property (
        @(posedge clk) disable iff (1'b0)
        COUT == ((A & B) | (A & CI) | (B & CI))
    );

    // The outputs match the two-bit addition of A, B, and CI.
    check_outputs_match_binary_addition: assert property (
        @(posedge clk) disable iff (1'b0)
        {COUT, SUM} == ({1'b0, A} + {1'b0, B} + {1'b0, CI})
    );

    // All-zero inputs produce zero carry and zero sum.
    check_zero_input_case: assert property (
        @(posedge clk) disable iff (1'b0)
        (!A && !B && !CI) |-> (!COUT && !SUM)
    );

    // Any one-hot input combination produces sum only.
    check_onehot_input_case: assert property (
        @(posedge clk) disable iff (1'b0)
        ((A && !B && !CI) || (!A && B && !CI) || (!A && !B && CI)) |-> (!COUT && SUM)
    );

    // Any two-hot input combination produces carry only.
    check_twohot_input_case: assert property (
        @(posedge clk) disable iff (1'b0)
        ((A && B && !CI) || (A && !B && CI) || (!A && B && CI)) |-> (COUT && !SUM)
    );

    // All-one inputs produce both carry and sum.
    check_all_high_case: assert property (
        @(posedge clk) disable iff (1'b0)
        (A && B && CI) |-> (COUT && SUM)
    );

endmodule