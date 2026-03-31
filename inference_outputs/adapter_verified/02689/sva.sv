module bitwise_operators_sva (
    input logic clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [3:0] and_res,
    input logic [3:0] or_res,
    input logic [3:0] xor_res,
    input logic [3:0] not_res
);

// and_res must equal A & B.
    check_and_result: assert property (
        @(posedge clk) and_res == (A & B)
    );

// or_res must equal A | B.
    check_or_result: assert property (
        @(posedge clk) or_res == (A | B)
    );

// xor_res must equal A ^ B.
    check_xor_result: assert property (
        @(posedge clk) xor_res == (A ^ B)
    );

// not_res must equal ~A.
    check_not_result: assert property (
        @(posedge clk) not_res == ~A
    );

// and_res must be a subset of A.
    check_and_subset_a: assert property (
        @(posedge clk) (and_res & ~A) == 4'b0000
    );

// and_res must be a subset of B.
    check_and_subset_b: assert property (
        @(posedge clk) (and_res & ~B) == 4'b0000
    );

// or_res must contain A.
    check_or_superset_a: assert property (
        @(posedge clk) (or_res & ~A) == 4'b0000
    );

// or_res must contain B.
    check_or_superset_b: assert property (
        @(posedge clk) (or_res & ~B) == 4'b0000
    );

// xor_res must be disjoint from A.
    check_xor_disjoint_a: assert property (
        @(posedge clk) (xor_res & A) == 4'b0000
    );

// xor_res must be disjoint from B.
    check_xor_disjoint_b: assert property (
        @(posedge clk) (xor_res & B) == 4'b0000
    );

// not_res must be the bitwise inverse of A.
    check_not_inverse: assert property (
        @(posedge clk) (not_res | A) == 4'b1111
    );

endmodule
