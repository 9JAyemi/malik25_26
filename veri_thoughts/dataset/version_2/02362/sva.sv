module eight_bit_adder_sva (
    input logic CLK,
    input logic [7:0] a,
    input logic [7:0] b,
    input logic cin,
    input logic [7:0] s,
    input logic cout
);
    ///// Adder correctness /////
    // Outputs equal the 9-bit sum of inputs (explicit zero-extend avoids width ambiguity).
    check_full_sum_9bit: assert property (
        @(posedge CLK) {cout, s} == ({1'b0, a} + {1'b0, b} + cin)
    );

    // s equals the lower 8 bits of the 9-bit sum.
    check_s_low_bits: assert property (
        @(posedge CLK) s == ({1'b0, a} + {1'b0, b} + cin)[7:0]
    );

    // cout equals the MSB (bit 8) of the 9-bit sum.
    check_cout_high_bit: assert property(
        @(posedge CLK) cout == ({1'b0, a} + {1'b0, b} + cin)[8]
    );

    // Addition is commutative: swapping a and b does not change the result.
    check_commutativity: assert property (
        @(posedge CLK) {cout, s} == ({1'b0, b} + {1'b0, a} + cin)
    );

    // LSB of sum equals XOR of input LSBs and cin.
    check_lsb_xor: assert property (
        @(posedge CLK) s[0] == (a[0] ^ b[0] ^ cin)
    );

    // Identity: adding zero with cin=0 yields output equal to a.
    check_identity_b_zero_no_cin: assert property (
        @(posedge CLK) (b == 8'h00 && cin == 1'b0) |-> ({cout, s} == {1'b0, a})
    );

    // Identity: adding zero with cin=0 yields output equal to b.
    check_identity_a_zero_no_cin: assert property (
        @(posedge CLK) (a == 8'h00 && cin == 1'b0) |-> ({cout, s} == {1'b0, b})
    );

    // Specific case: 0 + 0 + 1 yields s=1 and cout=0.
    check_zero_plus_one: assert property (
        @(posedge CLK) (a == 8'h00 && b == 8'h00 && cin == 1'b1) |-> (s == 8'h01 && cout == 1'b0)
    );

    // Specific case: 0xFF + 0xFF + 1 -> s=0xFF, cout=1.
    check_ff_ff_plus_one: assert property (
        @(posedge CLK) (a == 8'hFF && b == 8'hFF && cin == 1'b1) |-> (s == 8'hFF && cout == 1'b1)
    );

    // Specific case: 0x80 + 0x80 + 0 -> s=0x00, cout=1.
    check_80_80_no_cin: assert property (
        @(posedge CLK) (a == 8'h80 && b == 8'h80 && cin == 1'b0) |-> (s == 8'h00 && cout == 1'b1)
    );
endmodule