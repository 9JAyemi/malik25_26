module four_bit_adder_sva (
    input logic [3:0] a,
    input logic [3:0] b,
    input logic       cin,
    input logic [3:0] sum,
    input logic       cout
);

    // Combinational DUT with no RTL clock or reset; sample on the formal global clock.

    // Bit 0 sum is the XOR of a[0], b[0], and cin.
    check_sum_bit0: assert property (
        @($global_clock) sum[0] == (a[0] ^ b[0] ^ cin)
    );

    // Lower two sum bits match a 2-bit addition with carry-in.
    check_sum_low2: assert property (
        @($global_clock) sum[1:0] == (a[1:0] + b[1:0] + cin)
    );

    // Lower three sum bits match a 3-bit addition with carry-in.
    check_sum_low3: assert property (
        @($global_clock) sum[2:0] == (a[2:0] + b[2:0] + cin)
    );

    // The 4-bit sum bus matches the low 4 bits of the addition.
    check_sum_bus: assert property (
        @($global_clock) sum == (a + b + cin)
    );

    // Carry-out matches the fifth bit of the zero-extended addition.
    check_carry_out: assert property (
        @($global_clock) cout == (({1'b0, a} + {1'b0, b} + {4'b0, cin})[4])
    );

    // The combined carry and sum equal the full 5-bit addition result.
    check_full_result: assert property (
        @($global_clock) {cout, sum} == ({1'b0, a} + {1'b0, b} + {4'b0, cin})
    );

    // Adding zero on b with no carry-in returns a and no carry-out.
    check_identity_b_zero: assert property (
        @($global_clock) (b == 4'b0000 && cin == 1'b0) |-> ({cout, sum} == {1'b0, a})
    );

    // Adding zero on a with no carry-in returns b and no carry-out.
    check_identity_a_zero: assert property (
        @($global_clock) (a == 4'b0000 && cin == 1'b0) |-> ({cout, sum} == {1'b0, b})
    );

    // Zero operands with carry-in one produce a value of one.
    check_zero_operands_with_carry: assert property (
        @($global_clock) (a == 4'b0000 && b == 4'b0000 && cin == 1'b1) |-> ({cout, sum} == 5'b00001)
    );

endmodule