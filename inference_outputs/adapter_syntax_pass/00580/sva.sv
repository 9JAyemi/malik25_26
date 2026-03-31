module binary_subtractor_32bit_sva (
    input logic CLK,
    input logic [31:0] A,
    input logic [31:0] B,
    input logic [31:0] S
);
    // S equals A + (~B + 1) (two's complement subtraction).
    check_twos_complement_relation: assert property (
        @(posedge CLK) S == (A + ((~B) + 32'd1))
    );

    // If B is zero, S equals A (no borrow).
    check_b_zero_passthrough: assert property (
        @(posedge CLK) (B == 32'd0) |-> (S == A)
    );

    // If A is zero, S equals ~B + 1 (two's complement of B).
    check_a_zero_result: assert property (
        @(posedge CLK) (A == 32'd0) |-> (S == ((~B) + 32'd1))
    );

    // If B is all ones, S equals ~A (two's complement of A).
    check_b_all_ones_result: assert property (
        @(posedge CLK) (B == 32'hFFFF_FFFF) |-> (S == (~A))
    );

    // If A and B are equal, S is zero (A + (~A + 1) == 0).
    check_equal_inputs_zero: assert property (
        @(posedge CLK) (A == B) |-> (S == 32'd0)
    );

    // If A is all ones and B is zero, S is all ones (A + 1 == 0xFFFF_FFFF).
    check_all_ones_minus_zero: assert property (
        @(posedge CLK) (A == 32'hFFFF_FFFF && B == 32'd0) |-> (S == 32'hFFFF_FFFF)
    );

    // If A is zero and B is all ones, S is zero (0 + (~0xFFFF_FFFF + 1) == 0).
    check_zero_minus_all_ones: assert property (
        @(posedge CLK) (A == 32'd0 && B == 32'hFFFF_FFFF) |-> (S == 32'd0)
    );

    // If A is all ones and B is all ones, S is one (0xFFFF_FFFF + (~0xFFFF_FFFF + 1) == 1).
    check_all_ones_minus_all_ones: assert property (
        @(posedge CLK) (A == 32'hFFFF_FFFF && B == 32'hFFFF_FFFF) |-> (S == 32'd1)
    );

    // If A is zero and B is zero, S is zero (0 + (~0 + 1) == 0).
    check_zero_minus_zero: assert property (
        @(posedge CLK) (A == 32'd0 && B == 32'd0) |-> (S == 32'd0)
    );

    // If B is all ones and A is zero, S is one (0 + (~0xFFFF_FFFF + 1) == 1).
    check_zero_minus_all_ones: assert property (
        @(posedge CLK) (A == 32'd0 && B == 32'hFFFF_FFFF) |-> (S == 32'd1)
    );
endmodule