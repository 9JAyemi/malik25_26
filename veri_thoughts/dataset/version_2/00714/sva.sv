module calculator_sva (
    input logic clk,
    input logic [7:0] a_in,
    input logic [7:0] b_in,
    input logic [1:0] op,
    input logic [7:0] c_out
);
    // When op==00, output is 8-bit sum of a_in and b_in.
    check_add_result: assert property (
        @(posedge clk) (op == 2'b00) |-> (c_out == (a_in + b_in))
    );

    // When op==01, output is 8-bit difference a_in - b_in.
    check_sub_result: assert property (
        @(posedge clk) (op == 2'b01) |-> (c_out == (a_in - b_in))
    );

    // When op==10, output is low 8 bits of the product.
    check_mul_result_truncate8: assert property (
        @(posedge clk) (op == 2'b10) |-> (c_out == (a_in * b_in)[7:0])
    );

    // When op==11 and divisor is nonzero, output is a_in / b_in.
    check_div_result_nonzero: assert property (
        @(posedge clk) (op == 2'b11 && (b_in != 8'd0)) |-> (c_out == (a_in / b_in))
    );

    // If op contains any X/Z, default branch forces c_out to zero.
    check_default_on_unknown_op: assert property (
        @(posedge clk) $isunknown(op) |-> (c_out == 8'h00)
    );

    // If inputs are stable, output remains stable (pure combinational behavior).
    check_output_stable_when_inputs_stable: assert property (
        @(posedge clk) ($stable(a_in) && $stable(b_in) && $stable(op)) |-> $stable(c_out)
    );

    // Addition passthrough: when op==00 and b_in==0, c_out equals a_in.
    check_add_zero_b_passthru: assert property (
        @(posedge clk) (op == 2'b00 && (b_in == 8'd0)) |-> (c_out == a_in)
    );

    // Subtraction cancels equal operands: when op==01 and a_in==b_in, c_out==0.
    check_sub_equal_zero: assert property (
        @(posedge clk) (op == 2'b01 && (a_in == b_in)) |-> (c_out == 8'h00)
    );

    // Multiplication by zero yields zero when op==10.
    check_mul_zero_operand: assert property (
        @(posedge clk) (op == 2'b10 && ((a_in == 8'd0) || (b_in == 8'd0))) |-> (c_out == 8'h00)
    );

    // Division by one passes a_in through when op==11.
    check_div_by_one_passthru: assert property (
        @(posedge clk) (op == 2'b11 && (b_in == 8'd1)) |-> (c_out == a_in)
    );
endmodule