module fourBitAdder_sva (
    input logic clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic Cin,
    input logic [3:0] Sum,
    input logic Cout
);

// Sum must match the 4-bit addition of A, B, and Cin.
    check_full_add_result: assert property (
        @(posedge clk) {Cout, Sum} == ({1'b0, A} + {1'b0, B} + Cin)
    );

// Sum bit 0 must match the least-significant sum bit.
    check_sum_bit0: assert property (
        @(posedge clk) Sum[0] == (A[0] ^ B[0] ^ Cin)
    );

// Sum bit 1 must include the carry generated from bit 0.
    check_sum_bit1: assert property (
        @(posedge clk) Sum[1] == (A[1] ^ B[1] ^ ((A[0] & B[0]) | (A[0] & Cin) | (B[0] & Cin)))
    );

// Sum bit 2 must include the carry propagated through bits 0 and 1.
    check_sum_bit2: assert property (
        @(posedge clk) Sum[2] == (A[2] ^ B[2] ^
                                 ((A[1] & B[1]) |
                                  (A[1] & ((A[0] & B[0]) | (A[0] & Cin) | (B[0] & Cin))) |
                                  (B[1] & ((A[0] & B[0]) | (A[0] & Cin) | (B[0] & Cin)))))
    );

// Sum bit 3 must include the carry propagated through bits 0 through 2.
    check_sum_bit3: assert property (
        @(posedge clk) Sum[3] == (A[3] ^ B[3] ^
                                 ((A[2] & B[2]) |
                                  (A[2] & ((A[1] & B[1]) |
                                           (A[1] & ((A[0] & B[0]) | (A[0] & Cin) | (B[0] & Cin))) |
                                           (B[1] & ((A[0] & B[0]) | (A[0] & Cin) | (B[0] & Cin))))) |
                                  (B[2] & ((A[1] & B[1]) |
                                           (A[1] & ((A[0] & B[0]) | (A[0] & Cin) | (B[0] & Cin))) |
                                           (B[1] & ((A[0] & B[0]) | (A[0] & Cin) | (B[0] & Cin)))))))
    );

// Cout must match the carry out of the 4-bit addition.
    check_cout: assert property (
        @(posedge clk) Cout == ((A[3] & B[3]) |
                               (A[3] & ((A[2] & B[2]) |
                                        (A[2] & ((A[1] & B[1]) |
                                                 (A[1] & ((A[0] & B[0]) | (A[0] & Cin) | (B[0] & Cin))) |
                                                 (B[1] & ((A[0] & B[0]) | (A[0] & Cin) | (B[0] & Cin))))) |
                               (B[3] & ((A[2] & B[2]) |
                                        (A[2] & ((A[1] & B[1]) |
                                                 (A[1] & ((A[0] & B[0]) | (A[0] & Cin) | (B[0] & Cin))) |
                                                 (B[1] & ((A[0] & B[0]) | (A[0] & Cin) | (B[0] & Cin))))) |
                               (B[2] & ((A[1] & B[1]) |
                                        (A[1] & ((A[0] & B[0]) | (A[0] & Cin) | (B[0] & Cin))) |
                                        (B[1] & ((A[0] & B[0]) | (A[0] & Cin) | (B[0] & Cin)))))))
    );

endmodule
