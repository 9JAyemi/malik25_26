module logic_function_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic Ci,
    input logic S,
    input logic Co
);

    // No clock or reset exists in the RTL; sample on an external clock.
    // Sum output matches the implemented XOR-of-three function.
    check_sum_function: assert property (
        @(posedge clk) S == (A ^ B ^ Ci)
    );

    // When A and B are equal, sum follows Ci.
    check_sum_equal_ab: assert property (
        @(posedge clk) (A == B) |-> (S == Ci)
    );

    // When A and B differ, sum is the inverse of Ci.
    check_sum_different_ab: assert property (
        @(posedge clk) (A != B) |-> (S == ~Ci)
    );

    // Carry output matches the implemented A & (B | Ci) function.
    check_carry_function: assert property (
        @(posedge clk) Co == (A & (B | Ci))
    );

    // Carry can only assert when A is high.
    check_carry_requires_a: assert property (
        @(posedge clk) Co |-> A
    );

    // A and B high must assert carry.
    check_carry_from_ab: assert property (
        @(posedge clk) (A & B) |-> Co
    );

    // A and Ci high must assert carry.
    check_carry_from_aci: assert property (
        @(posedge clk) (A & Ci) |-> Co
    );

    // A low must force carry low.
    check_no_carry_when_a_low: assert property (
        @(posedge clk) (!A) |-> (!Co)
    );

    // With only A high, carry must remain low.
    check_no_carry_with_a_only: assert property (
        @(posedge clk) (A & !B & !Ci) |-> (!Co)
    );

endmodule