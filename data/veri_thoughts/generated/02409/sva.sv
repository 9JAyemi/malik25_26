module arithmetic_module_sva (
    input logic clk,
    input logic signed [31:0] a,
    input logic signed [31:0] b,
    input logic [1:0] op,
    input logic signed [31:0] c
);
    ///// Operation selection checks /////
    // When op==00, c must equal a+b (signed 32-bit).
    check_add_mapping: assert property (
        @(posedge clk) (op == 2'b00) |-> (c == (a + b))
    );

    // When op==01, c must equal a-b (signed 32-bit).
    check_sub_mapping: assert property (
        @(posedge clk) (op == 2'b01) |-> (c == (a - b))
    );

    // When op==10, c must equal a*b (signed 32-bit).
    check_mul_mapping: assert property (
        @(posedge clk) (op == 2'b10) |-> (c == (a * b))
    );

    // When op==11 and b!=0, c must equal a/b (signed 32-bit).
    check_div_mapping_no_zero: assert property (
        @(posedge clk) ((op == 2'b11) && (b != 32'sd0)) |-> (c == (a / b))
    );

    ///// Basic arithmetic identities (guarded) /////
    // Adding zero leaves a unchanged.
    check_zero_add_rhs: assert property (
        @(posedge clk) ((op == 2'b00) && (b == 32'sd0)) |-> (c == a)
    );

    // Subtracting zero leaves a unchanged.
    check_zero_sub_rhs: assert property (
        @(posedge clk) ((op == 2'b01) && (b == 32'sd0)) |-> (c == a)
    );

    // Multiplying by zero yields zero.
    check_zero_mul_operand: assert property (
        @(posedge clk) ((op == 2'b10) && ((a == 32'sd0) || (b == 32'sd0))) |-> (c == 32'sd0)
    );

    // Division by +1 yields a (when defined).
    check_identity_div_by_one: assert property (
        @(posedge clk) ((op == 2'b11) && (b == 32'sd1)) |-> (c == a)
    );

    // Division by -1 yields -a (when defined).
    check_negate_div_by_neg_one: assert property (
        @(posedge clk) ((op == 2'b11) && (b == -32'sd1)) |-> (c == -a)
    );

    // Zero dividend yields zero (when division is defined).
    check_zero_dividend: assert property (
        @(posedge clk) ((op == 2'b11) && (b != 32'sd0) && (a == 32'sd0)) |-> (c == 32'sd0)
    );

    ///// Combinational consistency /////
    // If a,b,op are stable across a cycle, c must also be stable.
    check_output_stable_when_inputs_stable: assert property (
        @(posedge clk) $stable({a,b,op}) |-> $stable(c)
    );
endmodule