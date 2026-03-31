module adder_4bit_sva (
    input logic       clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic       Cin,
    input logic [3:0] S,
    input logic       Cout
);

// Bit 0 sum matches the full-adder equation.
    check_sum_bit0: assert property (
        @(posedge clk) S[0] == (A[0] ^ B[0] ^ Cin)
    );

// Bit 1 sum uses the carry generated from bit 0.
    check_sum_bit1: assert property (
        @(posedge clk) S[1] == (A[1] ^ B[1] ^ ((A[0] & B[0]) | (A[0] & Cin) | (B[0] & Cin)))
    );

// Bit 2 sum uses the carry generated from bit 1.
    check_sum_bit2: assert property (
        @(posedge clk) S[2] == (A[2] ^ B[2] ^ (
            (A[1] & B[1]) |
            (A[1] & ((A[0] & B[0]) | (A[0] & Cin) | (B[0] & Cin))) |
            (B[1] & ((A[0] & B[0]) | (A[0] & Cin) | (B[0] & Cin)))
        ))
    );

// Bit 3 sum uses the carry generated from bit 2.
    check_sum_bit3: assert property (
        @(posedge clk) S[3] == (A[3] ^ B[3] ^ (
            (A[2] & B[2]) |
            (A[2] & (
                (A[1] & B[1]) |
                (A[1] & ((A[0] & B[0]) | (A[0] & Cin) | (B[0] & Cin))) |
                (B[1] & ((A[0] & B[0]) | (A[0] & Cin) | (B[0] & Cin)))
            )) |
            (B[2] & (
                (A[1] & B[1]) |
                (A[1] & ((A[0] & B[0]) | (A[0] & Cin) | (B[0] & Cin))) |
                (B[1] & ((A[0] & B[0]) | (A[0] & Cin) | (B[0] & Cin)))
            ))
        ))
    );

// Cout matches the carry-out equation from the final full-adder.
    check_cout: assert property (
        @(posedge clk) Cout == (
            (A[3] & B[3]) |
            (A[3] & (
                (A[2] & B[2]) |
                (A[2] & (
                    (A[1] & B[1]) |
                    (A[1] & ((A[0] & B[0]) | (A[0] & Cin) | (B[0] & Cin))) |
                    (B[1] & ((A[0] & B[0]) | (A[0] & Cin) | (B[0] & Cin)))
                )) |
                (B[2] & (
                    (A[1] & B[1]) |
                    (A[1] & ((A[0] & B[0]) | (A[0] & Cin) | (B[0] & Cin))) |
                    (B[1] & ((A[0] & B[0]) | (A[0] & Cin) | (B[0] & Cin)))
                ))
            )) |
            (B[3] & (
                (A[2] & B[2]) |
                (A[2] & (
                    (A[1] & B[1]) |
                    (A[1] & ((A[0] & B[0]) | (A[0] & Cin) | (B[0] & Cin))) |
                    (B[1] & ((A[0] & B[0]) | (A[0] & Cin) | (B[0] & Cin)))
                )) |
                (B[2] & (
                    (A[1] & B[1]) |
                    (A[1] & ((A[0] & B[0]) | (A[0] & Cin) | (B[0] & Cin))) |
                    (B[1] & ((A[0] & B[0]) | (A[0] & Cin) | (B[0] & Cin)))
                ))
            ))
        )
    );

endmodule
