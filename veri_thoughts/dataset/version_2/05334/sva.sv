module full_adder_32_sva (
    input logic        clk,
    input logic [31:0] A,
    input logic [31:0] B,
    input logic [31:0] Cin,
    input logic [31:0] Sum,
    input logic        Cout
);

    // Sampling clock only; the DUT is combinational and has no reset.

    // Full result matches A + B + Cin[0].
    check_full_add_value: assert property (
        @(posedge clk)
        {Cout, Sum} == ({1'b0, A} + {1'b0, B} + {{32{1'b0}}, Cin[0]})
    );

    // Sum bit 0 is the XOR of the input LSBs and Cin[0].
    check_lsb_sum_xor: assert property (
        @(posedge clk)
        Sum[0] == (A[0] ^ B[0] ^ Cin[0])
    );

    // Sum bit 1 uses the carry generated from bit 0.
    check_bit1_sum_with_bit0_carry: assert property (
        @(posedge clk)
        Sum[1] == (A[1] ^ B[1] ^ ((A[0] & B[0]) | (A[0] & Cin[0]) | (B[0] & Cin[0])))
    );

    // Sum bit 31 uses the carry from the lower 31-bit addition.
    check_msb_sum_with_lower_carry: assert property (
        @(posedge clk)
        Sum[31] == (A[31] ^ B[31] ^ (({1'b0, A[30:0]} + {1'b0, B[30:0]} + {{31{1'b0}}, Cin[0]})[31]))
    );

    // Cout is the carry-out of the 32-bit addition.
    check_cout_is_addition_carry: assert property (
        @(posedge clk)
        Cout == (({1'b0, A} + {1'b0, B} + {{32{1'b0}}, Cin[0]})[32])
    );

    // Zero operands leave only Cin[0] in Sum[0] and no carry-out.
    check_zero_inputs_behavior: assert property (
        @(posedge clk)
        (A == 32'h0000_0000 && B == 32'h0000_0000) |-> (Sum == {31'h0, Cin[0]} && Cout == 1'b0)
    );

    // With B zero and Cin[0] low, the adder passes A through.
    check_a_passthrough: assert property (
        @(posedge clk)
        (B == 32'h0000_0000 && Cin[0] == 1'b0) |-> (Sum == A && Cout == 1'b0)
    );

    // With A zero and Cin[0] low, the adder passes B through.
    check_b_passthrough: assert property (
        @(posedge clk)
        (A == 32'h0000_0000 && Cin[0] == 1'b0) |-> (Sum == B && Cout == 1'b0)
    );

    // Adding Cin[0] to all ones overflows and wraps Sum to zero.
    check_all_ones_plus_cin_overflow: assert property (
        @(posedge clk)
        (A == 32'hffff_ffff && B == 32'h0000_0000 && Cin[0] == 1'b1) |-> (Sum == 32'h0000_0000 && Cout == 1'b1)
    );

endmodule