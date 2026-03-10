module binary_subtractor_32bit_sva (
    input logic clk,
    input logic [31:0] A,
    input logic [31:0] B,
    input logic [31:0] S
);
    ///// Functional mapping /////
    // S implements A + (~B + 1), i.e., two's-complement subtraction.
    check_subtractor_function: assert property (
        @(posedge clk) S == (A + ((~B) + 32'd1))
    );

    // Adding B back to S yields A (mod 2^32).
    check_add_back_B_yields_A: assert property (
        @(posedge clk) (S + B) == A
    );

    // A minus S equals B (mod 2^32).
    check_A_minus_S_equals_B: assert property (
        @(posedge clk) A + ((~S) + 32'd1) == B
    );

    ///// Special cases /////
    // If inputs are equal, result is zero.
    check_equal_inputs_zero_output: assert property (
        @(posedge clk) (A == B) |-> (S == 32'd0)
    );

    // If B is zero, S passes through A.
    check_zero_B_passthrough: assert property (
        @(posedge clk) (B == 32'd0) |-> (S == A)
    );

    // If A is zero, S is two's complement of B.
    check_zero_A_twos_complement_B: assert property (
        @(posedge clk) (A == 32'd0) |-> (S == ((~B) + 32'd1))
    );

    // If B is all ones, S equals A plus one (mod 2^32).
    check_B_all_ones_inc_A: assert property (
        @(posedge clk) (B == 32'hFFFF_FFFF) |-> (S == (A + 32'd1))
    );

    ///// Structural/combinational behavior /////
    // If A and B are stable, S must be stable.
    check_stability_when_inputs_stable: assert property (
        @(posedge clk) ($stable(A) && $stable(B)) |-> $stable(S)
    );

    // LSB of result equals XOR of input LSBs.
    check_lsb_is_xor: assert property (
        @(posedge clk) S[0] == (A[0] ^ B[0])
    );

    // With B stable, S delta equals A delta (mod 2^32).
    check_delta_conservation_when_B_stable: assert property (
        @(posedge clk) $stable(B) |-> ( S + ((~$past(S)) + 32'd1) ) == ( A + ((~$past(A)) + 32'd1) )
    );
endmodule