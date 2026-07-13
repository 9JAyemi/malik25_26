module adder_sva(
    input logic clk,
    input logic [3:0] a,
    input logic [3:0] b,
    input logic [3:0] sum,
    input logic carry
);

    // Packed outputs must equal the zero-extended 4-bit add result.
    check_packed_output: assert property (
        @(posedge clk) {carry, sum} == {1'b0, (a + b)}
    );

    // Carry is always low because the add result is only 4 bits wide.
    check_carry_low: assert property (
        @(posedge clk) carry == 1'b0
    );

    // Sum must match the 4-bit addition result.
    check_sum_result: assert property (
        @(posedge clk) sum == (a + b)
    );

    // Zero on a passes b through with no carry.
    check_a_zero_passthrough: assert property (
        @(posedge clk) (a == 4'h0) |-> ((sum == b) && (carry == 1'b0))
    );

    // Zero on b passes a through with no carry.
    check_b_zero_passthrough: assert property (
        @(posedge clk) (b == 4'h0) |-> ((sum == a) && (carry == 1'b0))
    );

    // 4'hF plus 4'h1 truncates to zero with no carry.
    check_f_plus_one_truncates: assert property (
        @(posedge clk) ((a == 4'hF) && (b == 4'h1)) |-> ((sum == 4'h0) && (carry == 1'b0))
    );

    // 4'hF plus 4'hF truncates to 4'hE with no carry.
    check_max_plus_max_truncates: assert property (
        @(posedge clk) ((a == 4'hF) && (b == 4'hF)) |-> ((sum == 4'hE) && (carry == 1'b0))
    );

endmodule