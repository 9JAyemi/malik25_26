module top_module_sva (
    input logic clk,
    input logic [7:0] a,
    input logic [7:0] b,
    input logic [7:0] sum
);

    // Sum must equal the 8-bit addition of a and b.
    check_sum_matches_addition: assert property (
        @(posedge clk) sum == (a + b)
    );

    // The least-significant sum bit must match the full-adder XOR equation.
    check_lsb_sum_equation: assert property (
        @(posedge clk) sum[0] == (a[0] ^ b[0] ^ 1'b0)
    );

    // Adding zero on b must pass a through to the sum.
    check_b_zero_passthrough: assert property (
        @(posedge clk) (b == 8'h00) |-> (sum == a)
    );

    // Adding zero on a must pass b through to the sum.
    check_a_zero_passthrough: assert property (
        @(posedge clk) (a == 8'h00) |-> (sum == b)
    );

    // Adding equal operands must produce an even result.
    check_equal_operands_even_sum: assert property (
        @(posedge clk) (a == b) |-> (sum[0] == 1'b0)
    );

    // Adding 8'hFF and 8'h01 must wrap the 8-bit result to zero.
    check_ff_plus_one_wraps_to_zero: assert property (
        @(posedge clk) ((a == 8'hFF) && (b == 8'h01)) |-> (sum == 8'h00)
    );

    // Adding 8'h80 and 8'h80 must produce 8'h00 with no carry-out.
    check_80_plus_80_wraps_to_zero: assert property (
        @(posedge clk) ((a == 8'h80) && (b == 8'h80)) |-> (sum == 8'h00)
    );

    // Adding 8'hFF and 8'hFF must produce 8'hFE with no carry-out.
    check_ff_plus_ff_wraps_to_fe: assert property (
        @(posedge clk) ((a == 8'hFF) && (b == 8'hFF)) |-> (sum == 8'hFE)
    );

endmodule