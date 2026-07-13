module four_bit_adder_sva (
    input logic clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic Cin,
    input logic [3:0] S,
    input logic Cout
);

// Sum bit 0 matches the RTL XOR chain.
    check_sum_bit0: assert property (
        @(posedge clk) S[0] == (A[0] ^ B[0] ^ Cin)
    );

// Sum bit 1 uses the carry generated from bit 0.
    check_sum_bit1: assert property (
        @(posedge clk) S[1] == (A[1] ^ B[1] ^ carry_from_bit0)
    );

// Sum bit 2 uses the carry generated from bit 1.
    check_sum_bit2: assert property (
        @(posedge clk) S[2] == (A[2] ^ B[2] ^ carry_from_bit1)
    );

// Sum bit 3 uses the carry generated from bit 2.
    check_sum_bit3: assert property (
        @(posedge clk) S[3] == (A[3] ^ B[3] ^ carry_from_bit2)
    );

// Cout matches the RTL carry-out equation.
    check_cout_equation: assert property (
        @(posedge clk) Cout == (A[3] & B[3]) | (A[3] & carry_from_bit2) | (B[3] & carry_from_bit2)
    );

// Cout is high when bit 3 and bit 2 are both high.
    check_cout_bit3_bit2: assert property (
        @(posedge clk) (A[3] & B[3]) |-> Cout
    );

// Cout is high when bit 3 and bit 1 are both high.
    check_cout_bit3_bit1: assert property (
        @(posedge clk) (A[3] & B[3] & A[2] & B[2]) |-> Cout
    );

// Cout is high when bit 3 and bit 0 are both high.
    check_cout_bit3_bit0: assert property (
        @(posedge clk) (A[3] & B[3] & A[2] & B[2] & A[1] & B[1]) |-> Cout
    );

// Cout is high when bit 2, bit 1, and bit 0 are all high.
    check_cout_bit2_bit1_bit0: assert property (
        @(posedge clk) (A[2] & B[2] & A[1] & B[1] & A[0] & B[0]) |-> Cout
    );

// Cout is low when all four input bits are low.
    check_cout_all_zero: assert property (
        @(posedge clk) !(A[3] | B[3] | A[2] | B[2] | A[1] | B[1] | A[0] | B[0]) |-> !Cout
    );

endmodule
