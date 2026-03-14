module carry_save_adder_sva (
    input logic CLK,
    input logic [3:0] a,
    input logic [3:0] b,
    input logic [3:0] c,
    input logic [3:0] s,
    input logic [3:0] c_out
);
    // Sum is bitwise XOR of a, b, and c.
    check_sum_is_xor3: assert property (
        @(posedge CLK) disable iff (1'b0) s == (a ^ b) ^ c
    );

    // Carry-out equals (a & b) | (c & (a ^ b)).
    check_carry_function: assert property (
        @(posedge CLK) disable iff (1'b0) c_out == ((a & b) | (c & (a ^ b)))
    );

    // Carry-out equals majority function (a&b)|(a&c)|(b&c).
    check_carry_majority_equiv: assert property (
        @(posedge CLK) disable iff (1'b0) c_out == ((a & b) | (a & c) | (b & c))
    );

    // s OR c_out equals bitwise OR of inputs.
    check_sum_or_carry_matches_input_or: assert property (
        @(posedge CLK) disable iff (1'b0) (s | c_out) == (a | b | c)
    );

    // s AND c_out equals bitwise AND of all three inputs.
    check_sum_and_carry_triplet_and: assert property (
        @(posedge CLK) disable iff (1'b0) (s & c_out) == (a & b & c)
    );

    // When c is zero, sum reduces to a ^ b.
    check_sum_when_c_zero: assert property (
        @(posedge CLK) disable iff (1'b0) (c == 4'b0000) |-> (s == (a ^ b))
    );

    // When c is zero, carry reduces to a & b.
    check_carry_when_c_zero: assert property (
        @(posedge CLK) disable iff (1'b0) (c == 4'b0000) |-> (c_out == (a & b))
    );

    // When c is all ones, sum is bitwise NOT of (a ^ b).
    check_sum_when_c_ones: assert property (
        @(posedge CLK) disable iff (1'b0) (c == 4'b1111) |-> (s == ~(a ^ b))
    );

    // When c is all ones, carry is a | b.
    check_carry_when_c_ones: assert property (
        @(posedge CLK) disable iff (1'b0) (c == 4'b1111) |-> (c_out == (a | b))
    );

    // When a equals b, sum equals c.
    check_sum_when_a_eq_b: assert property (
        @(posedge CLK) disable iff (1'b0) (a == b) |-> (s == c)
    );

    // When c equals a ^ b, sum is zero.
    check_sum_when_c_eq_xor: assert property (
        @(posedge CLK) disable iff (1'b0) (c == (a ^ b)) |-> (s == 4'b0000)
    );

    // When c equals a ^ b, carry is a | b.
    check_carry_when_c_eq_xor: assert property (
        @(posedge CLK) disable iff (1'b0) (c == (a ^ b)) |-> (c_out == (a | b))
    );
endmodule