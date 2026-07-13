module adder4bit_sva (
    input  logic        clk,
    input  logic [3:0]  A,
    input  logic [3:0]  B,
    input  logic        Cin,
    input  logic [3:0]  Sum,
    input  logic        Cout
);
    // Sum/Cout equal the 5-bit unsigned result of A + B + Cin.
    check_total_sum: assert property (
        @(posedge clk) {Cout, Sum} == ({1'b0, A} + {1'b0, B} + Cin)
    );

    // Bit0 sum is XOR of A[0], B[0], and Cin.
    check_sum_bit0: assert property (
        @(posedge clk) Sum[0] == (A[0] ^ B[0] ^ Cin)
    );

    // Bit1 sum equals XOR with carry from bit0.
    check_sum_bit1: assert property (
        @(posedge clk) Sum[1] == (A[1] ^ B[1] ^ ((A[0] & B[0]) | (Cin & (A[0] ^ B[0]))))
    );

    // Bit2 sum equals XOR with carry from bit1.
    check_sum_bit2: assert property (
        @(posedge clk) Sum[2] == (A[2] ^ B[2] ^ (
            (A[1] & B[1]) | ((A[1] ^ B[1]) & ((A[0] & B[0]) | (Cin & (A[0] ^ B[0]))))
        ))
    );

    // Bit3 sum equals XOR with carry from bit2.
    check_sum_bit3: assert property (
        @(posedge clk) Sum[3] == (A[3] ^ B[3] ^ (
            (A[2] & B[2]) | ((A[2] ^ B[2]) &
                ((A[1] & B[1]) | ((A[1] ^ B[1]) & ((A[0] & B[0]) | (Cin & (A[0] ^ B[0])))))
            )
        ))
    );

    // Cout equals carry from bit3.
    check_cout: assert property (
        @(posedge clk) Cout == (
            (A[3] & B[3]) | ((A[3] ^ B[3]) &
                ((A[2] & B[2]) | ((A[2] ^ B[2]) &
                    ((A[1] & B[1]) | ((A[1] ^ B[1]) &
                        ((A[0] & B[0]) | (Cin & (A[0] ^ B[0])))
                    ))
                ))
            )
        )
    );
endmodule