module binary_multiplier_sva (
    input logic clk,
    input logic [7:0] a,
    input logic [7:0] b,
    input logic [15:0] result
);

    // Result must equal the zero-extended product of the two inputs.
    check_result_matches_product: assert property (
        @(posedge clk) result == ({8'b0, a} * {8'b0, b})
    );

    // A zero operand must produce a zero result.
    check_zero_operand_forces_zero_result: assert property (
        @(posedge clk) ((a == 8'h00) || (b == 8'h00)) |-> (result == 16'h0000)
    );

    // Multiplying by one on a must pass b through to the result.
    check_a_one_passthrough: assert property (
        @(posedge clk) (a == 8'h01) |-> (result == {8'b0, b})
    );

    // Multiplying by one on b must pass a through to the result.
    check_b_one_passthrough: assert property (
        @(posedge clk) (b == 8'h01) |-> (result == {8'b0, a})
    );

    // Multiplying by eight on a must shift b three bits left.
    check_a_eight_shift: assert property (
        @(posedge clk) (a == 8'h08) |-> (result == ({8'b0, b} << 3))
    );

    // Multiplying by eight on b must shift a three bits left.
    check_b_eight_shift: assert property (
        @(posedge clk) (b == 8'h08) |-> (result == ({8'b0, a} << 3))
    );

    // Multiplying by 16 on a must shift b four bits left.
    check_a_sixteen_shift: assert property (
        @(posedge clk) (a == 8'h10) |-> (result == ({8'b0, b} << 4))
    );

    // Multiplying by 16 on b must shift a four bits left.
    check_b_sixteen_shift: assert property (
        @(posedge clk) (b == 8'h10) |-> (result == ({8'b0, a} << 4))
    );

endmodule