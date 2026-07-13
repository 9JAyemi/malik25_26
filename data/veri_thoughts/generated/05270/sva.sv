module ripple_carry_adder_sva (
    input logic clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic Cin,
    input logic [3:0] S,
    input logic Cout
);

    // DUT is purely combinational and has no reset; clk is a sampling clock.

    // The 5-bit output must equal A + B + Cin.
    check_total_sum: assert property (
        @(posedge clk) {Cout, S} == ({1'b0, A} + {1'b0, B} + Cin)
    );

    // The least-significant sum bit is the XOR of the LSB inputs and carry-in.
    check_lsb_sum: assert property (
        @(posedge clk) S[0] == (A[0] ^ B[0] ^ Cin)
    );

    // Bit 1 must use the carry generated from bit 0.
    check_bit1_ripple: assert property (
        @(posedge clk) S[1] == (A[1] ^ B[1] ^ ((A[0] & B[0]) | (A[0] & Cin) | (B[0] & Cin)))
    );

    // Adding zero with no carry-in must reproduce A with no carry-out.
    check_add_zero_to_a: assert property (
        @(posedge clk) (B == 4'h0 && Cin == 1'b0) |-> ({Cout, S} == {1'b0, A})
    );

    // Adding zero with no carry-in must reproduce B with no carry-out.
    check_add_zero_to_b: assert property (
        @(posedge clk) (A == 4'h0 && Cin == 1'b0) |-> ({Cout, S} == {1'b0, B})
    );

    // All-zero inputs must produce a zero result.
    check_all_zero_inputs: assert property (
        @(posedge clk) (A == 4'h0 && B == 4'h0 && Cin == 1'b0) |-> ({Cout, S} == 5'h00)
    );

    // Carry-in alone must increment the zero input case to 1.
    check_cin_only: assert property (
        @(posedge clk) (A == 4'h0 && B == 4'h0 && Cin == 1'b1) |-> ({Cout, S} == 5'h01)
    );

    // Carry-out must be high exactly when the arithmetic result is 16 or more.
    check_cout_overflow: assert property (
        @(posedge clk) Cout == (({1'b0, A} + {1'b0, B} + Cin) >= 5'd16)
    );

    // Maximum operands without carry-in must produce 0xE with carry-out.
    check_max_operands_no_cin: assert property (
        @(posedge clk) (A == 4'hF && B == 4'hF && Cin == 1'b0) |-> ({Cout, S} == 5'h1E)
    );

    // Maximum operands with carry-in must produce 0xF with carry-out.
    check_max_operands_with_cin: assert property (
        @(posedge clk) (A == 4'hF && B == 4'hF && Cin == 1'b1) |-> ({Cout, S} == 5'h1F)
    );

endmodule