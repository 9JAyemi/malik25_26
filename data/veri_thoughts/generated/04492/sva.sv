module add4_carry_sva (
    input logic       clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic       Cin,
    input logic [3:0] Sum,
    input logic       Cout
);

    // No RTL clock or reset; sample this combinational DUT with clk.

    // Bit 0 sum matches the first full-adder XOR.
    check_sum_bit0_xor: assert property (
        @(posedge clk)
        Sum[0] == (A[0] ^ B[0] ^ Cin)
    );

    // Lower 2 sum bits match adding A[1:0], B[1:0], and Cin.
    check_lower_two_bits_add: assert property (
        @(posedge clk)
        Sum[1:0] == (({1'b0, A[1:0]} + {1'b0, B[1:0]} + Cin)[1:0])
    );

    // Lower 3 sum bits match adding A[2:0], B[2:0], and Cin.
    check_lower_three_bits_add: assert property (
        @(posedge clk)
        Sum[2:0] == (({1'b0, A[2:0]} + {1'b0, B[2:0]} + Cin)[2:0])
    );

    // All sum bits match 4-bit addition of A, B, and Cin.
    check_sum_vector_add: assert property (
        @(posedge clk)
        Sum == (({1'b0, A} + {1'b0, B} + Cin)[3:0])
    );

    // Cout matches the carry-out of the 4-bit addition.
    check_cout_add: assert property (
        @(posedge clk)
        Cout == (({1'b0, A} + {1'b0, B} + Cin)[4])
    );

    // The combined result equals the full 5-bit addition result.
    check_full_addition_result: assert property (
        @(posedge clk)
        {Cout, Sum} == ({1'b0, A} + {1'b0, B} + Cin)
    );

    // With unchanged inputs across samples, outputs also remain unchanged.
    check_stable_inputs_hold_outputs: assert property (
        @(posedge clk)
        $stable({A, B, Cin}) |-> $stable({Sum, Cout})
    );

endmodule