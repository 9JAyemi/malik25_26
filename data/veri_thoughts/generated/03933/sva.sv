module logic_function_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic Ci,
    input logic S,
    input logic Co
);

    // Sum output matches the XOR of A, B, and Ci.
    check_sum_function: assert property (
        @(posedge clk) S == (A ^ B ^ Ci)
    );

    // Carry output matches Ci gated by A and B being equal.
    check_carry_function: assert property (
        @(posedge clk) Co == (Ci & ~(A ^ B))
    );

    // Carry must be LOW whenever carry-in is LOW.
    check_carry_requires_ci: assert property (
        @(posedge clk) !Ci |-> !Co
    );

    // Carry must be LOW whenever A and B differ.
    check_carry_low_when_inputs_differ: assert property (
        @(posedge clk) (A ^ B) |-> !Co
    );

    // Carry follows Ci whenever A and B are equal.
    check_carry_follows_ci_when_inputs_equal: assert property (
        @(posedge clk) (A == B) |-> (Co == Ci)
    );

    // Sum follows Ci whenever A and B are equal.
    check_sum_follows_ci_when_inputs_equal: assert property (
        @(posedge clk) (A == B) |-> (S == Ci)
    );

    // Sum is the inverse of Ci whenever A and B differ.
    check_sum_inverts_ci_when_inputs_differ: assert property (
        @(posedge clk) (A != B) |-> (S == ~Ci)
    );

endmodule