module calculator_sva (
    input logic clk,
    input logic [7:0] a,
    input logic [7:0] b,
    input logic [1:0] op,
    input logic [7:0] result
);
    // When op==00, result equals low 8 bits of a + b.
    check_add_correct: assert property (
        @(posedge clk) (op == 2'b00) |-> (result == (a + b)[7:0])
    );

    // When op==01, result equals low 8 bits of a - b.
    check_sub_correct: assert property (
        @(posedge clk) (op == 2'b01) |-> (result == (a - b)[7:0])
    );

    // When op==10, result equals low 8 bits of a * b.
    check_mul_correct: assert property (
        @(posedge clk) (op == 2'b10) |-> (result == (a * b)[7:0])
    );

    // When op==11 and b!=0, result equals a / b.
    check_div_correct_nonzero: assert property (
        @(posedge clk) (op == 2'b11 && b != 8'd0) |-> (result == (a / b))
    );

    // If inputs are stable and not dividing by zero, result must be stable.
    check_stable_when_inputs_stable: assert property (
        @(posedge clk) ($stable(a) && $stable(b) && $stable(op) && !(op == 2'b11 && b == 8'd0)) |-> $stable(result)
    );
endmodule