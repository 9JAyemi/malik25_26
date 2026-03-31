module half_adder_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic sum,
    input logic carry_out
);

// sum must equal A ^ B.
    check_sum_xor: assert property (
        @(posedge clk) sum == (A ^ B)
    );

// carry_out must equal A & B.
    check_carry_and: assert property (
        @(posedge clk) carry_out == (A & B)
    );

// When both inputs are 0, sum must be 0.
    check_sum_zero_when_both_zero: assert property (
        @(posedge clk) (!A && !B) |-> (sum == 1'b0)
    );

// When both inputs are 1, sum must be 1.
    check_sum_one_when_both_one: assert property (
        @(posedge clk) (A && B) |-> (sum == 1'b1)
    );

// When A is 0 and B is 1, sum must be 1.
    check_sum_one_when_a_zero_b_one: assert property (
        @(posedge clk) (!A && B) |-> (sum == 1'b1)
    );

// When A is 1 and B is 0, sum must be 1.
    check_sum_one_when_a_one_b_zero: assert property (
        @(posedge clk) (A && !B) |-> (sum == 1'b1)
    );

// When A is 0 and B is 1, carry_out must be 0.
    check_carry_zero_when_a_zero_b_one: assert property (
        @(posedge clk) (!A && B) |-> (carry_out == 1'b0)
    );

// When A is 1 and B is 0, carry_out must be 0.
    check_carry_zero_when_a_one_b_zero: assert property (
        @(posedge clk) (A && !B) |-> (carry_out == 1'b0)
    );

// When both inputs are 1, carry_out must be 1.
    check_carry_one_when_both_one: assert property (
        @(posedge clk) (A && B) |-> (carry_out == 1'b1)
    );

endmodule
