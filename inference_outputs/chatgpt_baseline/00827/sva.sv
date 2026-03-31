module test_sva (
    input logic clk,
    input logic [7:0] a,
    input logic [7:0] b,
    input logic [7:0] out
);
    // When a >= b, out must equal a.
    check_out_eq_a_when_a_ge_b: assert property (
        @(posedge clk) (a >= b) |-> (out == a)
    );

    // When b > a, out must equal b.
    check_out_eq_b_when_b_gt_a: assert property (
        @(posedge clk) (b > a) |-> (out == b)
    );

    // When a == b, out must equal a.
    check_out_eq_a_when_equal: assert property (
        @(posedge clk) (a == b) |-> (out == a)
    );

    // If neither condition holds, out is 0.
    check_out_zero_when_neither: assert property (
        @(posedge clk) (!(a >= b) && !(b > a)) |-> (out == 8'h00)
    );

    // Under a >= b, out is at least b.
    check_out_ge_b_when_a_ge_b: assert property (
        @(posedge clk) (a >= b) |-> (out >= b)
    );

    // Under b > a, out is at least a.
    check_out_ge_a_when_b_gt_a: assert property (
        @(posedge clk) (b > a) |-> (out >= a)
    );
endmodule