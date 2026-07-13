module adder_sva (
    input  logic        CLK,
    input  logic [7:0]  A,
    input  logic [7:0]  B,
    input  logic [7:0]  C,
    input  logic        CARRY
);
    // Outputs equal full 9-bit unsigned sum of inputs.
    check_full_sum_equivalence: assert property (
        @(posedge CLK) {CARRY, C} == ({1'b0, A} + {1'b0, B})
    );
    // C equals the low 8 bits of A+B.
    check_c_low8: assert property (
        @(posedge CLK) C == (({1'b0, A} + {1'b0, B})[7:0])
    );
    // CARRY equals the 9th bit of A+B.
    check_carry_msb: assert property (
        @(posedge CLK) CARRY == (({1'b0, A} + {1'b0, B})[8])
    );
    // When A is zero, output mirrors B and carry is zero.
    check_when_A_zero: assert property (
        @(posedge CLK) (A == 8'h00) |-> (C == B) && (CARRY == 1'b0)
    );
    // When B is zero, output mirrors A and carry is zero.
    check_when_B_zero: assert property (
        @(posedge CLK) (B == 8'h00) |-> (C == A) && (CARRY == 1'b0)
    );
    // When A is 0xFF, C = B-1 and carry reflects B!=0.
    check_when_A_ff: assert property (
        @(posedge CLK) (A == 8'hFF) |-> (C == (B - 8'h01)) && (CARRY == (B != 8'h00))
    );
    // When B is 0xFF, C = A-1 and carry reflects A!=0.
    check_when_B_ff: assert property (
        @(posedge CLK) (B == 8'hFF) |-> (C == (A - 8'h01)) && (CARRY == (A != 8'h00))
    );
    // No overflow implies result is at least each operand.
    check_no_overflow_ge_operands: assert property (
        @(posedge CLK) (!CARRY) |-> (C >= A) && (C >= B)
    );
    // Overflow implies result is less than both operands.
    check_overflow_lt_operands: assert property (
        @(posedge CLK) (CARRY) |-> (C < A) && (C < B)
    );
    // LSB of sum equals XOR of operand LSBs (no carry-in).
    check_lsb_xor: assert property (
        @(posedge CLK) C[0] == (A[0] ^ B[0])
    );
endmodule