module multiplier_sva (
    input logic clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [7:0] OUT
);

    // OUT must match the full 4x4 product.
    check_exact_product: assert property (
        @(posedge clk) {8'b0, OUT} == ({4'b0, A} * {4'b0, B})
    );

    // The product LSB must be the AND of the operand LSBs.
    check_lsb_product: assert property (
        @(posedge clk) OUT[0] == (A[0] & B[0])
    );

    // A equal to zero must force the product to zero.
    check_zero_operand_a: assert property (
        @(posedge clk) (A == 4'd0) |-> (OUT == 8'd0)
    );

    // B equal to zero must force the product to zero.
    check_zero_operand_b: assert property (
        @(posedge clk) (B == 4'd0) |-> (OUT == 8'd0)
    );

    // A equal to one must pass B through to the output.
    check_unit_operand_a: assert property (
        @(posedge clk) (A == 4'd1) |-> (OUT == {4'b0, B})
    );

    // B equal to one must pass A through to the output.
    check_unit_operand_b: assert property (
        @(posedge clk) (B == 4'd1) |-> (OUT == {4'b0, A})
    );

    // B equal to two must produce A shifted left by one.
    check_shift_by_one: assert property (
        @(posedge clk) (B == 4'd2) |-> (OUT == ({4'b0, A} << 1))
    );

    // B equal to four must produce A shifted left by two.
    check_shift_by_two: assert property (
        @(posedge clk) (B == 4'd4) |-> (OUT == ({4'b0, A} << 2))
    );

    // B equal to eight must produce A shifted left by three.
    check_shift_by_three: assert property (
        @(posedge clk) (B == 4'd8) |-> (OUT == ({4'b0, A} << 3))
    );

    // The maximum 4-bit operands must produce 225.
    check_max_operands: assert property (
        @(posedge clk) ((A == 4'hf) && (B == 4'hf)) |-> (OUT == 8'he1)
    );

endmodule