module Adder4_sva (
    input logic [3:0] A,
    input logic [3:0] B,
    input logic       Cin,
    input logic       clk,
    input logic [3:0] S,
    input logic       Cout
);

    // S registers the 4-bit sum A+B+Cin one cycle later.
    check_sum_registered: assert property (
        @(posedge clk) 1'b1 |-> ##1 (S == $past(A + B + Cin))
    );

    // Cout registers the MSB carry expression one cycle later.
    check_cout_registered: assert property (
        @(posedge clk) 1'b1 |-> ##1 (Cout == $past((A[3] & B[3]) | (A[3] & Cin) | (B[3] & Cin)))
    );

    // LSB of the sum equals A[0]^B[0]^Cin one cycle later.
    check_sum_lsb_bit0: assert property (
        @(posedge clk) 1'b1 |-> ##1 (S[0] == $past(A[0] ^ B[0] ^ Cin))
    );

    // MSB of the sum equals bit[3] of (A+B+Cin) one cycle later.
    check_sum_msb_bit3: assert property (
        @(posedge clk) 1'b1 |-> ##1 (S[3] == $past((A + B + Cin)[3]))
    );

    // Cout is independent of lower bits; if {A[3],B[3],Cin} is unchanged across two cycles, Cout holds.
    check_cout_independent_of_lower_bits: assert property (
        @(posedge clk) ($past({A[3], B[3], Cin}) == $past({A[3], B[3], Cin}, 2)) |-> ##1 (Cout == $past(Cout))
    );

endmodule