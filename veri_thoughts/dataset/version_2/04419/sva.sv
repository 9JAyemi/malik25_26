module comparator_sva (
    input logic clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [3:0] C,
    input logic [3:0] D,
    input logic EQ,
    input logic GT
);

    // Exact input match drives EQ high and GT low.
    check_equal_case: assert property (
        @(posedge clk) ((A == B) && (C == D)) |-> ((EQ == 1'b1) && (GT == 1'b0))
    );

    // A greater than B drives GT high and EQ low.
    check_gt_a_greater: assert property (
        @(posedge clk) (A > B) |-> ((EQ == 1'b0) && (GT == 1'b1))
    );

    // With A tied to B, C greater than D drives GT high and EQ low.
    check_gt_tiebreak_case: assert property (
        @(posedge clk) ((A == B) && (C > D)) |-> ((EQ == 1'b0) && (GT == 1'b1))
    );

    // Lexicographically smaller inputs drive both outputs low.
    check_less_than_case: assert property (
        @(posedge clk) ((A < B) || ((A == B) && (C < D))) |-> ((EQ == 1'b0) && (GT == 1'b0))
    );

    // EQ can only be high on an exact match.
    check_eq_only_on_exact_match: assert property (
        @(posedge clk) (EQ == 1'b1) |-> ((A == B) && (C == D))
    );

    // GT can only be high on a lexicographic greater-than result.
    check_gt_only_on_greater_than: assert property (
        @(posedge clk) (GT == 1'b1) |-> ((A > B) || ((A == B) && (C > D)))
    );

    // Both outputs low means the inputs are lexicographically smaller.
    check_zero_outputs_mean_less_than: assert property (
        @(posedge clk) ((EQ == 1'b0) && (GT == 1'b0)) |-> ((A < B) || ((A == B) && (C < D)))
    );

    // EQ and GT are never asserted together.
    check_output_mutex: assert property (
        @(posedge clk) !((EQ == 1'b1) && (GT == 1'b1))
    );

endmodule