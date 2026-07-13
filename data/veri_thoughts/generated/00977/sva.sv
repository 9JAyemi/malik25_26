module addsub_sva (
    input logic clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic sel,
    input logic [3:0] sum,
    input logic cout
);
    // When sel=0, sum equals 4-bit A+B.
    check_sum_add_path: assert property (
        @(posedge clk) (sel == 1'b0) |-> (sum == (A + B))
    );

    // When sel=1, sum equals 4-bit A + (~B + 1).
    check_sum_sub_path: assert property (
        @(posedge clk) (sel == 1'b1) |-> (sum == (A + (~B + 4'b0001)))
    );

    // When sel=0, cout indicates carry by sum < A.
    check_cout_add_path: assert property (
        @(posedge clk) (sel == 1'b0) |-> (cout == (sum < A))
    );

    // When sel=1, cout indicates borrow by A < B.
    check_cout_sub_path: assert property (
        @(posedge clk) (sel == 1'b1) |-> (cout == (A < B))
    );

    // When sel=0, cout equals MSB of 5-bit A+B.
    check_add_carry_bit_equivalence: assert property (
        @(posedge clk) (sel == 1'b0) |-> (cout == ({1'b0, A} + {1'b0, B})[4])
    );

    // When sel=0, (sum - A) mod 16 equals B.
    check_add_inverse_relation_sum_minus_A_eq_B: assert property (
        @(posedge clk) (sel == 1'b0) |-> ((sum + (~A + 4'b0001)) == B)
    );

    // When sel=1, (sum + B) mod 16 equals A.
    check_sub_inverse_relation_sum_plus_B_eq_A: assert property (
        @(posedge clk) (sel == 1'b1) |-> ((sum + B) == A)
    );

    // When sel=0 and B==0, sum==A and no carry.
    check_add_B_zero_case: assert property (
        @(posedge clk) ((sel == 1'b0) && (B == 4'b0000)) |-> ((sum == A) && (cout == 1'b0))
    );

    // When sel=1 and B==0, sum==A and no borrow.
    check_sub_B_zero_case: assert property (
        @(posedge clk) ((sel == 1'b1) && (B == 4'b0000)) |-> ((sum == A) && (cout == 1'b0))
    );

    // When sel=1 and A==B, sum==0 and no borrow.
    check_sub_equal_operands_yield_zero: assert property (
        @(posedge clk) ((sel == 1'b1) && (A == B)) |-> ((sum == 4'b0000) && (cout == 1'b0))
    );

    // When sel=1 and borrow occurs, result wraps above A.
    check_sub_borrow_implies_sum_gt_A: assert property (
        @(posedge clk) ((sel == 1'b1) && (cout == 1'b1)) |-> (sum > A)
    );

    // When sel=1 and no borrow, result is <= A.
    check_sub_no_borrow_implies_sum_le_A: assert property (
        @(posedge clk) ((sel == 1'b1) && (cout == 1'b0)) |-> (sum <= A)
    );
endmodule