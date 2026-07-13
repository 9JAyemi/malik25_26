module four_bit_adder_sva (
    input logic [3:0] A,
    input logic [3:0] B,
    input logic       Cin,
    input logic [3:0] Sum,
    input logic       Cout
);
    // No clock/reset in DUT; combinational logic; use $global_clock for sampling.

    // Local let expressions for ripple carries derived from DUT equations
    let c1 = (A[0] & B[0]) | (B[0] & Cin) | (A[0] & Cin);
    let c2 = (A[1] & B[1]) | (B[1] & c1)  | (A[1] & c1);
    let c3 = (A[2] & B[2]) | (B[2] & c2)  | (A[2] & c2);

    ///// Functional correctness /////
    // 5-bit sum equals A + B + Cin.
    check_full_sum: assert property (
        @(posedge $global_clock) {Cout, Sum} == ({1'b0, A} + {1'b0, B} + Cin)
    );
    // Sum low 4 bits match truncated addition.
    check_sum_low4: assert property (
        @(posedge $global_clock) Sum == (({1'b0, A} + {1'b0, B} + Cin)[3:0])
    );
    // Cout equals MSB of 5-bit addition result.
    check_cout_msb: assert property (
        @(posedge $global_clock) Cout == (({1'b0, A} + {1'b0, B} + Cin)[4])
    );

    ///// Bit-slice correctness /////
    // LSB sum implements XOR of A[0], B[0], Cin.
    check_sum0_xor: assert property (
        @(posedge $global_clock) Sum[0] == (A[0] ^ B[0] ^ Cin)
    );
    // Bit1 sum uses carry c1 from bit0.
    check_sum1_xor: assert property (
        @(posedge $global_clock) Sum[1] == (A[1] ^ B[1] ^ c1)
    );
    // Bit2 sum uses carry c2 from bit1.
    check_sum2_xor: assert property (
        @(posedge $global_clock) Sum[2] == (A[2] ^ B[2] ^ c2)
    );
    // Bit3 sum uses carry c3 from bit2.
    check_sum3_xor: assert property (
        @(posedge $global_clock) Sum[3] == (A[3] ^ B[3] ^ c3)
    );
    // Cout is majority of A[3], B[3], and c3.
    check_cout_majority: assert property (
        @(posedge $global_clock) Cout == ((A[3] & B[3]) | (B[3] & c3) | (A[3] & c3))
    );

    ///// Basic identities /////
    // Adding zero B and zero Cin returns A with no carry.
    check_add_zero_B: assert property (
        @(posedge $global_clock) ((B == 4'b0000) && (Cin == 1'b0)) |=> ((Sum == A) && (Cout == 1'b0))
    );
    // Adding zero A and zero Cin returns B with no carry.
    check_add_zero_A: assert property (
        @(posedge $global_clock) ((A == 4'b0000) && (Cin == 1'b0)) |=> ((Sum == B) && (Cout == 1'b0))
    );
endmodule