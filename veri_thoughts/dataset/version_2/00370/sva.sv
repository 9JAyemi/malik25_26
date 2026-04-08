module half_full_adder_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic C_in,
    input logic S,
    input logic C_out
);

    // Sum matches XOR of all three inputs.
    check_sum_equation: assert property (
        @(posedge clk) S == (A ^ B ^ C_in)
    );

    // Carry matches the implemented carry equation.
    check_carry_equation: assert property (
        @(posedge clk) C_out == ((A & B) | ((A ^ B) & C_in))
    );

    // Sum and carry match the 2-bit arithmetic result.
    check_arithmetic_result: assert property (
        @(posedge clk) {C_out, S} == ({1'b0, A} + {1'b0, B} + {1'b0, C_in})
    );

    // With no carry-in, the block behaves like a half-adder.
    check_no_carry_in_behavior: assert property (
        @(posedge clk) !C_in |-> ((S == (A ^ B)) && (C_out == (A & B)))
    );

    // When both inputs are low, sum follows C_in and carry is low.
    check_zero_operands: assert property (
        @(posedge clk) (!A && !B) |-> ((S == C_in) && (C_out == 1'b0))
    );

    // When both inputs are high, sum follows C_in and carry is high.
    check_both_operands_high: assert property (
        @(posedge clk) (A && B) |-> ((S == C_in) && (C_out == 1'b1))
    );

    // When A and B differ, carry follows C_in and sum inverts C_in.
    check_operands_different: assert property (
        @(posedge clk) (A ^ B) |-> ((S == ~C_in) && (C_out == C_in))
    );

endmodule