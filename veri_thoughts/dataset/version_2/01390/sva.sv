module csa_generate_adder_32bit_sva (
    input logic CLK,
    input logic [31:0] A,
    input logic [31:0] B,
    input logic [31:0] S,
    input logic C32
);
    // Functional equivalence: {C32,S} = {0,(A+B)} + {0,(A^B)} + {0..,A[31]&B[31]}.
    check_sum_definition: assert property (
        @(posedge CLK) {C32, S} == ({1'b0, (A + B)} + {1'b0, (A ^ B)} + {32'b0, (A[31] & B[31])})
    );

    // LSB of S equals MSB generate (A[31] & B[31]).
    check_s0_equals_msb_generate: assert property (
        @(posedge CLK) S[0] == (A[31] & B[31])
    );

    // Zero inputs yield zero outputs.
    check_zero_input_zero_output: assert property (
        @(posedge CLK) ((A == 32'd0) && (B == 32'd0)) |-> ((S == 32'd0) && (C32 == 1'b0))
    );

    // If B is zero, output equals 2*A (33-bit).
    check_b_zero_doubles_a: assert property (
        @(posedge CLK) (B == 32'd0) |-> ({C32, S} == ({1'b0, A} + {1'b0, A}))
    );

    // If A is zero, output equals 2*B (33-bit).
    check_a_zero_doubles_b: assert property (
        @(posedge CLK) (A == 32'd0) |-> ({C32, S} == ({1'b0, B} + {1'b0, B}))
    );

    // If inputs are equal, {C32,S} = {0,(A+B)} + {0..,A[31]}.
    check_equal_inputs_rule: assert property (
        @(posedge CLK) (A == B) |-> ({C32, S} == ({1'b0, (A + B)} + {32'b0, A[31]}))
    );

    // Complementary inputs (B == ~A) yield constant {1,0xFFFFFFFE}.
    check_complement_inputs_result: assert property (
        @(posedge CLK) (B == ~A) |-> ({C32, S} == 33'h1_FFFFFFFE)
    );

    // With B zero, carry-out equals A's MSB.
    check_b_zero_carry_equals_a31: assert property (
        @(posedge CLK) (B == 32'd0) |-> (C32 == A[31])
    );

    // With A zero, carry-out equals B's MSB.
    check_a_zero_carry_equals_b31: assert property (
        @(posedge CLK) (A == 32'd0) |-> (C32 == B[31])
    );
endmodule