module calculator_sva (
    input logic clk,
    input logic [7:0] a,
    input logic [7:0] b,
    input logic [1:0] op,
    input logic [7:0] result
);

    // 8-bit add (wraps to 8 bits)
    function automatic [7:0] add8 (input [7:0] x, input [7:0] y);
        add8 = x + y;
    endfunction
    // 8-bit sub (wraps to 8 bits)
    function automatic [7:0] sub8 (input [7:0] x, input [7:0] y);
        sub8 = x - y;
    endfunction
    // 8-bit mul (low 8 bits of product)
    function automatic [7:0] mul8 (input [7:0] x, input [7:0] y);
        mul8 = x * y;
    endfunction
    // 8-bit div (truncated integer divide)
    function automatic [7:0] div8 (input [7:0] x, input [7:0] y);
        div8 = x / y;
    endfunction

    ///// Functional correctness for each op /////
    // When op==00, result is 8-bit a+b (wrap).
    check_add_correct: assert property (
        @(posedge clk) (op == 2'b00) |-> (result == add8(a, b))
    );
    // When op==01, result is 8-bit a-b (wrap).
    check_sub_correct: assert property (
        @(posedge clk) (op == 2'b01) |-> (result == sub8(a, b))
    );
    // When op==10, result is low 8 bits of a*b.
    check_mul_correct: assert property (
        @(posedge clk) (op == 2'b10) |-> (result == mul8(a, b))
    );
    // When op==11, result is a/b (8-bit integer divide).
    check_div_correct: assert property (
        @(posedge clk) (op == 2'b11) |-> (result == div8(a, b))
    );

    ///// Combinational purity /////
    // If a, b, op are stable, result must be stable.
    check_stable_when_inputs_stable: assert property (
        @(posedge clk) $stable({a, b, op}) |-> $stable(result)
    );

    ///// Simple algebraic identities per operation /////
    // Add: +0 is identity.
    check_add_identity_b0: assert property (
        @(posedge clk) (op == 2'b00) && (b == 8'h00) |-> (result == a)
    );
    // Add: 0+ is identity.
    check_add_identity_a0: assert property (
        @(posedge clk) (op == 2'b00) && (a == 8'h00) |-> (result == b)
    );
    // Sub: -0 is identity.
    check_sub_identity_b0: assert property (
        @(posedge clk) (op == 2'b01) && (b == 8'h00) |-> (result == a)
    );
    // Sub: x-x = 0 (8-bit wrap).
    check_sub_self_zero: assert property (
        @(posedge clk) (op == 2'b01) && (a == b) |-> (result == 8'h00)
    );
    // Mul: 0 is annihilator.
    check_mul_zero: assert property (
        @(posedge clk) (op == 2'b10) && ((a == 8'h00) || (b == 8'h00)) |-> (result == 8'h00)
    );
    // Mul: 1 is identity (a*1 = a).
    check_mul_identity_b1: assert property (
        @(posedge clk) (op == 2'b10) && (b == 8'h01) |-> (result == a)
    );
    // Mul: 1 is identity (1*b = b).
    check_mul_identity_a1: assert property (
        @(posedge clk) (op == 2'b10) && (a == 8'h01) |-> (result == b)
    );
    // Div: /1 is identity.
    check_div_by_one: assert property (
        @(posedge clk) (op == 2'b11) && (b == 8'h01) |-> (result == a)
    );
    // Div: 0/x = 0 for nonzero x.
    check_div_zero_numer: assert property (
        @(posedge clk) (op == 2'b11) && (a == 8'h00) && (b != 8'h00) |-> (result == 8'h00)
    );
    // Div: x/x = 1 for nonzero x.
    check_div_self_one: assert property (
        @(posedge clk) (op == 2'b11) && (a == b) && (b != 8'h00) |-> (result == 8'h01)
    );

endmodule