module adder_sva (
    input logic [7:0] A,
    input logic [7:0] B,
    input logic [8:0] sum
);
    // No clock or reset in DUT; pure combinational; use immediate assertions.

    always_comb begin
        // Sum equals zero-extended addition of A and B.
        check_sum_equals_zero_extended_add: assert (sum == ({1'b0, A} + {1'b0, B}));

        // Lower 8 bits of sum equal A+B modulo 256.
        check_sum_lower_byte: assert (sum[7:0] == (A + B));

        // Carry-out bit equals bit[8] of the zero-extended addition.
        check_carry_bit_matches: assert (sum[8] == (({1'b0, A} + {1'b0, B})[8]));

        // Swapping operands does not change the result.
        check_commutative_result: assert (sum == ({1'b0, B} + {1'b0, A}));

        // Sum is at least each operand (unsigned).
        check_sum_ge_operands: assert ((sum >= {1'b0, A}) && (sum >= {1'b0, B}));
    end
endmodule