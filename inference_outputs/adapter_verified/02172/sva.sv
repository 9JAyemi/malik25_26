module ripple_adder_sva (
    input logic clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic Cin,
    input logic [3:0] S,
    input logic Cout
);

// Sum bit 0 matches the first full-adder XOR.
    check_sum_bit0: assert property (
        @(posedge clk) S[0] == (A[0] ^ B[0] ^ Cin)
    );

// Sum bit 1 uses the carry generated from bit 0.
    check_sum_bit1: assert property (
        @(posedge clk) S[1] == (A[1] ^ B[1] ^ ((A[0] & B[0]) | (A[0] & Cin) | (B[0] & Cin)))
    );

// Sum bit 2 uses the carry generated from bit 1.
    check_sum_bit2: assert property (
        @(posedge clk) S[2] == (A[2] ^ B[2] ^ (
            (A[1] & B[1]) |
            ((A[1] & (A[0] & B[0])) | (A[1] & (A[0] & Cin)) | (A[1] & (B[0] & Cin))) |
            ((B[1] & (A[0] & B[0])) | (B[1] & (A[0] & Cin)) | (B[1] & (B[0] & Cin)))
        ))
    );

// Sum bit 3 uses the carry generated from bit 2.
    check_sum_bit3: assert property (
        @(posedge clk) S[3] == (A[3] ^ B[3] ^ (
            (A[2] & B[2]) |
            ((A[2] & (A[1] & B[1])) | (A[2] & (A[1] & ((A[0] & B[0]) | (A[0] & Cin) | (B[0] & Cin)))) | (A[2] & (B[1] & ((A[0] & B[0]) | (A[0] & Cin) | (B[0] & Cin))))) |
            ((B[2] & (A[1] & B[1])) | (B[2] & (A[1] & ((A[0] & B[0]) | (A[0] & Cin) | (B[0] & Cin)))) | (B[2] & (B[1] & ((A[0] & B[0]) | (A[0] & Cin) | (B[0] & Cin)))))
        ))
    );

// Cout matches the carry generated from bit 3.
    check_cout: assert property (
        @(posedge clk) Cout == (
            (A[3] & B[3]) |
            ((A[3] & (A[2] & B[2])) | (A[3] & (A[2] & (A[1] & B[1]))) | (A[3] & (A[2] & ((A[1] & (A[0] & B[0])) | (A[1] & (A[0] & Cin)) | (A[1] & (B[0] & Cin)))) | (A[3] & (B[2] & ((A[1] & (A[0] & B[0])) | (A[1] & (A[0] & Cin)) | (A[1] & (B[0] & Cin))))))) |
            ((B[3] & (A[2] & B[2])) | (B[3] & (A[2] & (A[1] & B[1]))) | (B[3] & (A[2] & ((A[1] & (A[0] & B[0])) | (A[1] & (A[0] & Cin)) | (A[1] & (B[0] & Cin)))) | (B[3] & (B[2] & ((A[1] & (A[0] & B[0])) | (A[1] & (A[0] & Cin)) | (A[1] & (B[0] & Cin)))))))
        )
    );

// The 5-bit output matches the 4-bit A + 4-bit B + Cin.
    check_total_sum: assert property (
        @(posedge clk) {Cout, S} == ({1'b0, A} + {1'b0, B} + Cin)
    );

endmodule
