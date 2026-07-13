module four_bit_adder_sva (
    input logic clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic Cin,
    input logic [3:0] S,
    input logic Cout
);
    // Local recomputation of ripple carries for bit-level checks.
    logic c0, c1, c2;
    assign c0 = (A[0] & B[0]) | (A[0] & Cin) | (B[0] & Cin);
    assign c1 = (A[1] & B[1]) | (A[1] & c0) | (B[1] & c0);
    assign c2 = (A[2] & B[2]) | (A[2] & c1) | (B[2] & c1);

    ///// Functional correctness /////
    // Sum and carry-out equal the 5-bit unsigned addition of A, B, and Cin.
    check_full_sum: assert property (
        @(posedge clk) {Cout, S} == ({1'b0, A} + {1'b0, B} + Cin)
    );

    // LSB sum is XOR of A[0], B[0], and Cin.
    check_bit0_sum: assert property (
        @(posedge clk) S[0] == (A[0] ^ B[0] ^ Cin)
    );

    // Bit1 sum equals XOR of A[1], B[1], and carry from bit0.
    check_bit1_sum: assert property (
        @(posedge clk) S[1] == (A[1] ^ B[1] ^ c0)
    );

    // Bit2 sum equals XOR of A[2], B[2], and carry from bit1.
    check_bit2_sum: assert property (
        @(posedge clk) S[2] == (A[2] ^ B[2] ^ c1)
    );

    // Bit3 sum equals XOR of A[3], B[3], and carry from bit2.
    check_bit3_sum: assert property (
        @(posedge clk) S[3] == (A[3] ^ B[3] ^ c2)
    );

    // Carry-out equals majority of A[3], B[3], and carry from bit2.
    check_cout: assert property (
        @(posedge clk) Cout == ((A[3] & B[3]) | (A[3] & c2) | (B[3] & c2))
    );

    ///// Sanity cases derived from the adder definition /////
    // Adding zero with Cin=0 passes A through and Cout=0.
    check_add_zero_B: assert property (
        @(posedge clk) ((B == 4'b0000) && (Cin == 1'b0)) |-> ((S == A) && (Cout == 1'b0))
    );

    // Adding zero with Cin=0 passes B through and Cout=0.
    check_add_zero_A: assert property (
        @(posedge clk) ((A == 4'b0000) && (Cin == 1'b0)) |-> ((S == B) && (Cout == 1'b0))
    );

    // All-zero inputs produce all-zero outputs.
    check_all_zero: assert property (
        @(posedge clk) ((A == 4'b0000) && (B == 4'b0000) && (Cin == 1'b0)) |-> ((S == 4'b0000) && (Cout == 1'b0))
    );

    // Adding bitwise complement with Cin=1 yields S=0 and Cout=1 (A + ~A + 1 = 16).
    check_complement_plus_one: assert property (
        @(posedge clk) ((B == ~A) && (Cin == 1'b1)) |-> ((S == 4'b0000) && (Cout == 1'b1))
    );
endmodule