module ripple_carry_adder_sva (
    input logic clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic Cin,
    input logic [3:0] S,
    input logic Cout
);

    function automatic logic fa_sum (
        input logic a,
        input logic b,
        input logic cin
    );
        fa_sum = a ^ b ^ cin;
    endfunction

    function automatic logic fa_carry (
        input logic a,
        input logic b,
        input logic cin
    );
        fa_carry = (a & b) | ((a ^ b) & cin);
    endfunction

    // Bit 0 matches a full-adder result.
    check_bit0_result: assert property (
        @(posedge clk)
        {fa_carry(A[0], B[0], Cin), S[0]} == ({1'b0, A[0]} + {1'b0, B[0]} + Cin)
    );

    // Bit 1 sum uses the carry from bit 0.
    check_bit1_sum: assert property (
        @(posedge clk)
        S[1] == fa_sum(A[1], B[1], fa_carry(A[0], B[0], Cin))
    );

    // Bits [1:0] match 2-bit addition with carry-in.
    check_lower_two_bits: assert property (
        @(posedge clk)
        {fa_carry(A[1], B[1], fa_carry(A[0], B[0], Cin)), S[1:0]} ==
        ({1'b0, A[1:0]} + {1'b0, B[1:0]} + Cin)
    );

    // Bit 2 sum uses the propagated carry from bits [1:0].
    check_bit2_sum: assert property (
        @(posedge clk)
        S[2] == fa_sum(A[2], B[2],
                       fa_carry(A[1], B[1], fa_carry(A[0], B[0], Cin)))
    );

    // Bits [2:0] match 3-bit addition with carry-in.
    check_lower_three_bits: assert property (
        @(posedge clk)
        {fa_carry(A[2], B[2], fa_carry(A[1], B[1], fa_carry(A[0], B[0], Cin))), S[2:0]} ==
        ({1'b0, A[2:0]} + {1'b0, B[2:0]} + Cin)
    );

    // Bit 3 sum uses the propagated carry from bits [2:0].
    check_bit3_sum: assert property (
        @(posedge clk)
        S[3] == fa_sum(A[3], B[3],
                       fa_carry(A[2], B[2],
                                fa_carry(A[1], B[1], fa_carry(A[0], B[0], Cin))))
    );

    // Carry-out matches the final full-adder carry equation.
    check_final_carry: assert property (
        @(posedge clk)
        Cout == fa_carry(A[3], B[3],
                         fa_carry(A[2], B[2],
                                  fa_carry(A[1], B[1], fa_carry(A[0], B[0], Cin))))
    );

    // The full result matches 4-bit addition with carry-in.
    check_overall_addition: assert property (
        @(posedge clk)
        {Cout, S} == ({1'b0, A} + {1'b0, B} + Cin)
    );

    // With no carry-in, the result matches plain 4-bit addition.
    check_no_cin_plain_add: assert property (
        @(posedge clk)
        (Cin == 1'b0) |-> ({Cout, S} == ({1'b0, A} + {1'b0, B}))
    );

    // Adding a zero B operand leaves only A and carry-in.
    check_zero_b_operand: assert property (
        @(posedge clk)
        (B == 4'b0000) |-> ({Cout, S} == ({1'b0, A} + Cin))
    );

    // Adding a zero A operand leaves only B and carry-in.
    check_zero_a_operand: assert property (
        @(posedge clk)
        (A == 4'b0000) |-> ({Cout, S} == ({1'b0, B} + Cin))
    );

endmodule