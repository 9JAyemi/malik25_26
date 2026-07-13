module comparator_sva (
    input logic clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic EQ,
    input logic GT
);

// EQ must equal the bitwise AND of the inverted difference.
    check_eq_definition: assert property (
        @(posedge clk) EQ == (&(~(A - B)))
    );

// GT must equal the most-significant-bit of the difference AND the inverted MSB.
    check_gt_definition: assert property (
        @(posedge clk) GT == (A[3] & ~(A[3] - B[3]))
    );

// When A equals B, EQ must be high and GT must be low.
    check_equal_case: assert property (
        @(posedge clk) (A == B) |-> (EQ && !GT)
    );

// When A is greater than B, GT must be high and EQ must be low.
    check_greater_case: assert property (
        @(posedge clk) (A > B) |-> (GT && !EQ)
    );

// When A is less than B, neither EQ nor GT can be high.
    check_less_case: assert property (
        @(posedge clk) (A < B) |-> (!EQ && !GT)
    );

// EQ can only be high when A equals B.
    check_eq_only_on_equal: assert property (
        @(posedge clk) EQ |-> (A == B)
    );

// GT can only be high when A is greater than B.
    check_gt_only_on_greater: assert property (
        @(posedge clk) GT |-> (A > B)
    );

// EQ and GT cannot be high at the same time.
    check_mutex_eq_gt: assert property (
        @(posedge clk) !(EQ && GT)
    );

endmodule
