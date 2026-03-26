module FOURBITADDER_sva (
    input logic clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic Cin,
    input logic [3:0] S,
    input logic Cout
);

    function automatic logic fa_cout (
        input logic a,
        input logic b,
        input logic cin
    );
        fa_cout = (a & b) | (b & cin) | (a & cin);
    endfunction

    // The 5-bit result matches A + B + Cin.
    check_total_sum: assert property (
        @(posedge clk) {Cout, S} == ({1'b0, A} + {1'b0, B} + Cin)
    );

    // Sum bit 0 matches the first full-adder XOR.
    check_sum_bit0: assert property (
        @(posedge clk) S[0] == (A[0] ^ B[0] ^ Cin)
    );

    // Sum bit 1 uses the carry from bit 0.
    check_sum_bit1: assert property (
        @(posedge clk) S[1] == (A[1] ^ B[1] ^ fa_cout(A[0], B[0], Cin))
    );

    // Sum bit 2 uses the carry from bit 1.
    check_sum_bit2: assert property (
        @(posedge clk) S[2] == (A[2] ^ B[2] ^ fa_cout(A[1], B[1], fa_cout(A[0], B[0], Cin)))
    );

    // Sum bit 3 uses the carry from bit 2.
    check_sum_bit3: assert property (
        @(posedge clk) S[3] == (A[3] ^ B[3] ^ fa_cout(A[2], B[2], fa_cout(A[1], B[1], fa_cout(A[0], B[0], Cin))))
    );

    // Cout matches the last full-adder carry.
    check_cout: assert property (
        @(posedge clk) Cout == fa_cout(A[3], B[3], fa_cout(A[2], B[2], fa_cout(A[1], B[1], fa_cout(A[0], B[0], Cin))))
    );

endmodule