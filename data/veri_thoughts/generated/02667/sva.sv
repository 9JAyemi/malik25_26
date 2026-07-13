module calculator_sva (
    input logic clk,
    input logic [1:0] op,
    input logic [7:0] a,
    input logic [7:0] b,
    input logic reset,
    input logic [7:0] result,
    input logic valid
);
    // On reset, next-cycle result and valid are cleared.
    reset_clears_result_and_valid: assert property (
        @(posedge clk) reset |=> (result == 8'b0) && (valid == 1'b0)
    );

    // When not in reset, valid is HIGH on the next cycle.
    valid_next_cycle_when_not_reset: assert property (
        @(posedge clk) disable iff (reset) 1'b1 |=> (valid == 1'b1)
    );

    // After two consecutive non-reset cycles, valid must be HIGH.
    valid_stays_high_out_of_reset: assert property (
        @(posedge clk) disable iff (reset) (!reset && $past(!reset)) |-> (valid == 1'b1)
    );

    // ADD: Next-cycle result equals previous a+b (LSB 8) and valid HIGH.
    add_result_correct: assert property (
        @(posedge clk) disable iff (reset)
            (op == 2'b00) |=> ((result == (($past(a) + $past(b)) [7:0])) && (valid == 1'b1))
    );

    // SUB: Next-cycle result equals previous a-b (LSB 8) and valid HIGH.
    sub_result_correct: assert property (
        @(posedge clk) disable iff (reset)
            (op == 2'b01) |=> ((result == (($past(a) - $past(b)) [7:0])) && (valid == 1'b1))
    );

    // MUL: Next-cycle result equals previous a*b (LSB 8) and valid HIGH.
    mul_result_correct: assert property (
        @(posedge clk) disable iff (reset)
            (op == 2'b10) |=> ((result == (($past(a) * $past(b)) [7:0])) && (valid == 1'b1))
    );

    // DIV (b!=0): Next-cycle result equals previous a/b and valid HIGH.
    div_result_correct_when_b_nonzero: assert property (
        @(posedge clk) disable iff (reset)
            ((op == 2'b11) && (b != 8'd0)) |=> ((result == ($past(a) / $past(b))) && (valid == 1'b1))
    );

    // After ADD opcode, valid is HIGH on the next cycle.
    valid_after_add: assert property (
        @(posedge clk) disable iff (reset) (op == 2'b00) |=> (valid == 1'b1)
    );

    // After SUB opcode, valid is HIGH on the next cycle.
    valid_after_sub: assert property (
        @(posedge clk) disable iff (reset) (op == 2'b01) |=> (valid == 1'b1)
    );

    // After MUL opcode, valid is HIGH on the next cycle.
    valid_after_mul: assert property (
        @(posedge clk) disable iff (reset) (op == 2'b10) |=> (valid == 1'b1)
    );
endmodule