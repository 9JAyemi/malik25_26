module calculator_sva(
    input logic clk,
    input logic rst,
    input logic [1:0] op,
    input logic [3:0] num1,
    input logic [3:0] num2,
    input logic [3:0] result,
    input logic overflow
);

    // Addition selects the low 4 bits of num1 + num2.
    check_add_result: assert property (
        @(posedge clk) disable iff (rst)
        (op == 2'b00) |-> (result == ((num1 + num2) & 4'hF))
    );

    // Subtraction selects the low 4 bits of num1 - num2.
    check_sub_result: assert property (
        @(posedge clk) disable iff (rst)
        (op == 2'b01) |-> (result == ((num1 - num2) & 4'hF))
    );

    // Multiplication selects the low 4 bits of num1 * num2.
    check_mul_result: assert property (
        @(posedge clk) disable iff (rst)
        (op == 2'b10) |-> (result == ((num1 * num2) & 4'hF))
    );

    // Division selects the quotient when the divisor is nonzero.
    check_div_result: assert property (
        @(posedge clk) disable iff (rst)
        (op == 2'b11 && num2 != 4'd0) |-> (result == (num1 / num2))
    );

    // Overflow never asserts in this implementation.
    check_overflow_always_low: assert property (
        @(posedge clk) disable iff (rst)
        (overflow == 1'b0)
    );

    // Stable nonzero-divisor inputs keep the outputs stable.
    check_outputs_stable_for_stable_inputs: assert property (
        @(posedge clk) disable iff (rst)
        ($stable({op, num1, num2}) && !(op == 2'b11 && num2 == 4'd0))
        |-> $stable({result, overflow})
    );

endmodule