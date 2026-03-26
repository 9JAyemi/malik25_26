module adder4bit_sva (
    input logic [3:0] A,
    input logic [3:0] B,
    input logic Cin,
    input logic [3:0] Sum,
    input logic Cout,
    input logic clk
);

    // The 5-bit output matches A + B + Cin.
    check_total_addition: assert property (
        @(posedge clk) {Cout, Sum} == ({1'b0, A} + {1'b0, B} + Cin)
    );

    // The LSB sum bit is the XOR of A[0], B[0], and Cin.
    check_lsb_sum: assert property (
        @(posedge clk) Sum[0] == (A[0] ^ B[0] ^ Cin)
    );

    // With B at zero, the result is A plus Cin.
    check_add_zero_b: assert property (
        @(posedge clk) (B == 4'h0) |-> ({Cout, Sum} == ({1'b0, A} + Cin))
    );

    // With A at zero, the result is B plus Cin.
    check_add_zero_a: assert property (
        @(posedge clk) (A == 4'h0) |-> ({Cout, Sum} == ({1'b0, B} + Cin))
    );

    // If only bit 0 can contribute, bits above bit 1 must stay low.
    check_bit0_only_range: assert property (
        @(posedge clk) (A[3:1] == 3'b000 && B[3:1] == 3'b000) |-> (Sum[3:2] == 2'b00 && Cout == 1'b0)
    );

    // Adding 1 to 4'hF must ripple a carry through all four stages.
    check_full_carry_propagation: assert property (
        @(posedge clk) (A == 4'hF && B == 4'h0 && Cin == 1'b1) |-> (Sum == 4'h0 && Cout == 1'b1)
    );

    // A plus its bitwise complement with Cin set must produce zero with carry out.
    check_twos_complement_identity: assert property (
        @(posedge clk) (B == ~A && Cin == 1'b1) |-> (Sum == 4'h0 && Cout == 1'b1)
    );

    // A plus its bitwise complement with Cin clear must produce 4'hF.
    check_complement_without_carry_in: assert property (
        @(posedge clk) (B == ~A && Cin == 1'b0) |-> (Sum == 4'hF && Cout == 1'b0)
    );

    // With no lower-bit carry, the MSB stage behaves as a single full adder.
    check_msb_no_lower_carry: assert property (
        @(posedge clk) (A[2:0] == 3'b000 && B[2:0] == 3'b000 && Cin == 1'b0) |->
            (Sum[2:0] == 3'b000 && Sum[3] == (A[3] ^ B[3]) && Cout == (A[3] & B[3]))
    );

endmodule