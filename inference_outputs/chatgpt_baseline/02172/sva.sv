module ripple_adder_sva (
    input logic CLK,
    input logic RESETn,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic Cin,
    input logic [3:0] S,
    input logic Cout
);
    // Sum and carry equal A+B+Cin.
    check_sum_5bit: assert property (
        @(posedge CLK) disable iff (!RESETn)
        {Cout, S} == ({1'b0, A} + {1'b0, B} + Cin)
    );

    // S[0] equals bit 0 of A+B+Cin.
    check_bit0_from_add: assert property (
        @(posedge CLK) disable iff (!RESETn)
        S[0] == ({1'b0, A} + {1'b0, B} + Cin)[0]
    );

    // S[1] equals bit 1 of A+B+Cin.
    check_bit1_from_add: assert property (
        @(posedge CLK) disable iff (!RESETn)
        S[1] == ({1'b0, A} + {1'b0, B} + Cin)[1]
    );

    // Cout equals bit 4 of A+B+Cin.
    check_cout_from_add: assert property (
        @(posedge CLK) disable iff (!RESETn)
        Cout == ({1'b0, A} + {1'b0, B} + Cin)[4]
    );

    // S[0] is XOR of A[0], B[0], and Cin.
    check_bit0_xor: assert property (
        @(posedge CLK) disable iff (!RESETn)
        S[0] == (A[0] ^ B[0] ^ Cin)
    );

    // S[1] is XOR of A[1], B[1], and carry from bit0.
    check_bit1_chain: assert property (
        @(posedge CLK) disable iff (!RESETn)
        S[1] == (A[1] ^ B[1] ^ ((A[0] & B[0]) | ((A[0] ^ B[0]) & Cin)))
    );

    // S[2] is XOR of A[2], B[2], and carry from bit1.
    check_bit2_chain: assert property (
        @(posedge CLK) disable iff (!RESETn)
        S[2] == (A[2] ^ B[2] ^ (
                    (A[1] & B[1]) |
                    ((A[1] ^ B[1]) & ((A[0] & B[0]) | ((A[0] ^ B[0]) & Cin)))
                ))
    );

    // S[3] is XOR of A[3], B[3], and carry from bit2.
    check_bit3_chain: assert property (
        @(posedge CLK) disable iff (!RESETn)
        S[3] == (A[3] ^ B[3] ^ (
                    (A[2] & B[2]) |
                    ((A[2] ^ B[2]) & (
                        (A[1] & B[1]) |
                        ((A[1] ^ B[1]) & ((A[0] & B[0]) | ((A[0] ^ B[0]) & Cin)))
                    ))
                ))
    );

    // Cout equals carry from bit3.
    check_cout_chain: assert property (
        @(posedge CLK) disable iff (!RESETn)
        Cout == (
            (A[3] & B[3]) |
            ((A[3] ^ B[3]) & (
                (A[2] & B[2]) |
                ((A[2] ^ B[2]) & (
                    (A[1] & B[1]) |
                    ((A[1] ^ B[1]) & ((A[0] & B[0]) | ((A[0] ^ B[0]) & Cin)))
                ))
            ))
        )
    );

    // If A+B+Cin < 16 then Cout is 0.
    check_no_overflow_when_small: assert property (
        @(posedge CLK) disable iff (!RESETn)
        (({1'b0, A} + {1'b0, B} + Cin) <= 5'd15) |-> (Cout == 1'b0)
    );

    // If A+B+Cin >= 16 then Cout is 1.
    check_overflow_when_large: assert property (
        @(posedge CLK) disable iff (!RESETn)
        (({1'b0, A} + {1'b0, B} + Cin) >= 5'd16) |-> (Cout == 1'b1)
    );

    // With all inputs zero, outputs must be zero.
    check_zero_plus_zero: assert property (
        @(posedge CLK) disable iff (!RESETn)
        (A == 4'b0000) && (B == 4'b0000) && (Cin == 1'b0) |-> (S == 4'b0000) && (Cout == 1'b0)
    );
endmodule