module Test_sva (
    input logic clk,
    input logic [7:0] a,
    input logic [7:0] b,
    input logic [7:0] out
);

// When a is greater than or equal to b, out equals a.
    check_out_eq_a_when_a_ge_b: assert property (
        @(posedge clk) (a >= b) |-> (out == a)
    );

// When b is greater than a, out equals b.
    check_out_eq_b_when_b_gt_a: assert property (
        @(posedge clk) (b > a) |-> (out == b)
    );

// When a equals b, out is zero.
    check_out_zero_when_a_eq_b: assert property (
        @(posedge clk) (a == b) |-> (out == 8'h00)
    );

// When a is greater than b, out is not zero.
    check_out_not_zero_when_a_gt_b: assert property (
        @(posedge clk) (a > b) |-> (out != 8'h00)
    );

// When a is less than b, out is not zero.
    check_out_not_zero_when_a_lt_b: assert property (
        @(posedge clk) (a < b) |-> (out != 8'h00)
    );

// When a is equal to b, out is not equal to a.
    check_out_ne_a_when_a_eq_b: assert property (
        @(posedge clk) (a == b) |-> (out != a)
    );

// When a is greater than b, out is not equal to b.
    check_out_ne_b_when_a_gt_b: assert property (
        @(posedge clk) (a > b) |-> (out != b)
    );

// When b is greater than a, out is not equal to a.
    check_out_ne_a_when_b_gt_a: assert property (
        @(posedge clk) (b > a) |-> (out != a)
    );

endmodule
