module adder4bit_carry_sva (
    input logic clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic cin,
    input logic [3:0] S,
    input logic cout
);

    // Combined output must match the 5-bit sum of A, B, and cin.
    check_full_sum_relation: assert property (
        @(posedge clk) {cout, S} == ({1'b0, A} + {1'b0, B} + {4'b0000, cin})
    );

    // The least significant sum bit follows full-adder XOR behavior.
    check_lsb_sum_bit: assert property (
        @(posedge clk) S[0] == (A[0] ^ B[0] ^ cin)
    );

    // The next sum bit uses bit 0 carry as a full-adder would.
    check_bit1_sum_bit: assert property (
        @(posedge clk) S[1] == (A[1] ^ B[1] ^ ((A[0] & B[0]) | (A[0] & cin) | (B[0] & cin)))
    );

    // Carry-out is asserted when the arithmetic result is at least 16.
    check_carry_out_threshold: assert property (
        @(posedge clk) cout == (({1'b0, A} + {1'b0, B} + {4'b0000, cin}) >= 5'd16)
    );

    // Zero inputs must produce a zero sum and no carry-out.
    check_zero_addition: assert property (
        @(posedge clk) (A == 4'h0 && B == 4'h0 && cin == 1'b0) |-> (S == 4'h0 && cout == 1'b0)
    );

    // A passes through when B and cin are zero.
    check_a_passthrough: assert property (
        @(posedge clk) (B == 4'h0 && cin == 1'b0) |-> (S == A && cout == 1'b0)
    );

    // B passes through when A and cin are zero.
    check_b_passthrough: assert property (
        @(posedge clk) (A == 4'h0 && cin == 1'b0) |-> (S == B && cout == 1'b0)
    );

    // Carry-in increments A when B is zero.
    check_cin_increments_a: assert property (
        @(posedge clk) (B == 4'h0 && cin == 1'b1) |-> ({cout, S} == ({1'b0, A} + 5'd1))
    );

    // Carry-in increments B when A is zero.
    check_cin_increments_b: assert property (
        @(posedge clk) (A == 4'h0 && cin == 1'b1) |-> ({cout, S} == ({1'b0, B} + 5'd1))
    );

    // Adding bitwise complements without carry-in yields all ones and no carry.
    check_complement_without_carry: assert property (
        @(posedge clk) (B == ~A && cin == 1'b0) |-> (S == 4'hF && cout == 1'b0)
    );

    // Adding bitwise complements with carry-in yields zero and carry-out.
    check_complement_with_carry: assert property (
        @(posedge clk) (B == ~A && cin == 1'b1) |-> (S == 4'h0 && cout == 1'b1)
    );

endmodule