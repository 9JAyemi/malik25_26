module calc_sva (
    input logic CLK,
    input logic [7:0] a,
    input logic [7:0] b,
    input logic [1:0] op,
    input logic [7:0] result
);
    // When op=00, result equals 8-bit sum of a and b.
    check_add_is_sum: assert property (
        @(posedge CLK) disable iff (1'b0) (op == 2'b00) |-> (result == (a + b))
    );

    // When op=01, result equals 8-bit difference a - b.
    check_sub_is_diff: assert property (
        @(posedge CLK) disable iff (1'b0) (op == 2'b01) |-> (result == (a - b))
    );

    // When op=10, result equals low 8 bits of a*b.
    check_mul_is_lsb_product: assert property (
        @(posedge CLK) disable iff (1'b0) (op == 2'b10) |-> (result == ((a * b)[7:0]))
    );

    // When op=11 and b!=0, result equals a/b.
    check_div_is_quot_nonzero: assert property (
        @(posedge CLK) disable iff (1'b0) (op == 2'b11 && (b != 8'd0)) |-> (result == (a / b))
    );

    // Add with b==0 passes a through.
    check_add_zero_b_passthrough: assert property (
        @(posedge CLK) disable iff (1'b0) (op == 2'b00 && (b == 8'd0)) |-> (result == a)
    );

    // Add with a==0 passes b through.
    check_add_zero_a_passthrough: assert property (
        @(posedge CLK) disable iff (1'b0) (op == 2'b00 && (a == 8'd0)) |-> (result == b)
    );

    // Sub with a==b yields zero.
    check_sub_equal_operands_zero: assert property (
        @(posedge CLK) disable iff (1'b0) (op == 2'b01 && (a == b)) |-> (result == 8'd0)
    );

    // Mul with a==0 yields zero.
    check_mul_zero_a_zero: assert property (
        @(posedge CLK) disable iff (1'b0) (op == 2'b10 && (a == 8'd0)) |-> (result == 8'd0)
    );

    // Mul with b==0 yields zero.
    check_mul_zero_b_zero: assert property (
        @(posedge CLK) disable iff (1'b0) (op == 2'b10 && (b == 8'd0)) |-> (result == 8'd0)
    );

    // Mul with b==1 passes a through.
    check_mul_by_one_b_passthrough: assert property (
        @(posedge CLK) disable iff (1'b0) (op == 2'b10 && (b == 8'd1)) |-> (result == a)
    );

    // Mul with a==1 passes b through.
    check_mul_by_one_a_passthrough: assert property (
        @(posedge CLK) disable iff (1'b0) (op == 2'b10 && (a == 8'd1)) |-> (result == b)
    );

    // Div with b==1 passes a through.
    check_div_by_one_passthrough: assert property (
        @(posedge CLK) disable iff (1'b0) (op == 2'b11 && (b == 8'd1)) |-> (result == a)
    );
endmodule