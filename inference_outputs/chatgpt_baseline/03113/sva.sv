module addition_module_sva (
    input logic clk,
    input logic [7:0] A,
    input logic [7:0] B,
    input logic [8:0] sum,
    input logic carry
);

    // Sum is the zero-extended 8-bit result of A+B.
    check_sum_zero_extended_add: assert property (
        @(posedge clk) sum == {1'b0, (A + B)}
    );

    // The upper sum bit is always zero.
    check_sum_msb_zero: assert property (
        @(posedge clk) sum[8] == 1'b0
    );

    // Carry matches the upper bit of sum.
    check_carry_matches_sum_msb: assert property (
        @(posedge clk) carry == sum[8]
    );

    // Carry is always low.
    check_carry_zero: assert property (
        @(posedge clk) carry == 1'b0
    );

    // Zero inputs produce zero outputs.
    check_zero_plus_zero: assert property (
        @(posedge clk) (A == 8'h00 && B == 8'h00) |-> (sum == 9'h000 && carry == 1'b0)
    );

    // 0xFF + 0x01 wraps in 8 bits with no carry output.
    check_ff_plus_one_wraps: assert property (
        @(posedge clk) (A == 8'hFF && B == 8'h01) |-> (sum == 9'h000 && carry == 1'b0)
    );

endmodule