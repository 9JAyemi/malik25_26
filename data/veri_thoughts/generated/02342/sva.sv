module binary_adder_sva (
    input  logic clk,
    input  logic [3:0] A,
    input  logic [3:0] B,
    input  logic       Cin,
    input  logic [3:0] S,
    input  logic       Cout
);
    // Sum and carry match 4-bit addition with carry-in.
    check_total_sum: assert property (
        @(posedge clk) {Cout, S} == ({1'b0, A} + {1'b0, B} + Cin)
    );

    // LSB sum is XOR of A[0], B[0], and Cin.
    check_s0_is_xor: assert property (
        @(posedge clk) S[0] == (A[0] ^ B[0] ^ Cin)
    );

    // When A[1]==B[1], S[1] equals carry out from bit0.
    check_s1_matches_c1_when_a1_eq_b1: assert property (
        @(posedge clk)
        (A[1] == B[1]) |-> (S[1] == ((A[0] & B[0]) | (A[0] & Cin) | (B[0] & Cin)))
    );

    // When A[1]!=B[1], S[1] is inverse of carry out from bit0.
    check_s1_inverts_c1_when_a1_ne_b1: assert property (
        @(posedge clk)
        (A[1] ^ B[1]) |-> (S[1] == ~((A[0] & B[0]) | (A[0] & Cin) | (B[0] & Cin)))
    );

    // No overflow implies Cout is 0.
    check_cout_zero_when_no_overflow: assert property (
        @(posedge clk) (({1'b0, A} + {1'b0, B} + Cin) < 5'd16) |-> (Cout == 1'b0)
    );

    // Overflow implies Cout is 1.
    check_cout_one_when_overflow: assert property (
        @(posedge clk) (({1'b0, A} + {1'b0, B} + Cin) >= 5'd16) |-> (Cout == 1'b1)
    );

    // Adding zero B and zero Cin passes A through and no carry.
    check_add_zero_B_yields_A: assert property (
        @(posedge clk) ((B == 4'b0) && (Cin == 1'b0)) |-> ((S == A) && (Cout == 1'b0))
    );

    // Adding zero A and zero Cin passes B through and no carry.
    check_add_zero_A_yields_B: assert property (
        @(posedge clk) ((A == 4'b0) && (Cin == 1'b0)) |-> ((S == B) && (Cout == 1'b0))
    );

    // B is bitwise complement of A with Cin=0 yields S=0xF and no carry.
    check_complement_sum_all_ones: assert property (
        @(posedge clk) ((B == ~A) && (Cin == 1'b0)) |-> ((S == 4'hF) && (Cout == 1'b0))
    );

    // B is bitwise complement of A with Cin=1 yields S=0x0 and carry out.
    check_complement_with_cin_carryout: assert property (
        @(posedge clk) ((B == ~A) && (Cin == 1'b1)) |-> ((S == 4'h0) && (Cout == 1'b1))
    );

    // Outputs do not change when inputs hold constant.
    check_outputs_stable_when_inputs_stable: assert property (
        @(posedge clk) ($stable(A) && $stable(B) && $stable(Cin)) |-> ($stable(S) && $stable(Cout))
    );
endmodule