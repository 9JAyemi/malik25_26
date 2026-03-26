module four_bit_adder_sva (
    input logic clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic CIN,
    input logic [3:0] S,
    input logic COUT
);

    // Bit 0 sum matches the first full-adder XOR.
    check_sum_bit0: assert property (
        @(posedge clk)
        S[0] == (A[0] ^ B[0] ^ CIN)
    );

    // Bit 1 sum uses the carry generated from bit 0.
    check_sum_bit1: assert property (
        @(posedge clk)
        S[1] == (A[1] ^ B[1] ^
                 ((A[0] & B[0]) | (A[0] & CIN) | (B[0] & CIN)))
    );

    // The low three bits and COUT equal the 3-bit addition result.
    check_lower_three_bit_addition: assert property (
        @(posedge clk)
        {COUT, S[2:0]} == ({1'b0, A[2:0]} + {1'b0, B[2:0]} + CIN)
    );

    // Bit 2 sum uses the carry generated from bit 1.
    check_sum_bit2: assert property (
        @(posedge clk)
        S[2] == (A[2] ^ B[2] ^
                 ((A[1] & B[1]) |
                  (A[1] & ((A[0] & B[0]) | (A[0] & CIN) | (B[0] & CIN))) |
                  (B[1] & ((A[0] & B[0]) | (A[0] & CIN) | (B[0] & CIN)))))
    );

    // COUT is the carry out produced by the bit 2 full adder.
    check_cout_from_bit2: assert property (
        @(posedge clk)
        COUT == ((A[2] & B[2]) |
                 (A[2] & ((A[1] & B[1]) |
                          (A[1] & ((A[0] & B[0]) | (A[0] & CIN) | (B[0] & CIN))) |
                          (B[1] & ((A[0] & B[0]) | (A[0] & CIN) | (B[0] & CIN))))) |
                 (B[2] & ((A[1] & B[1]) |
                          (A[1] & ((A[0] & B[0]) | (A[0] & CIN) | (B[0] & CIN))) |
                          (B[1] & ((A[0] & B[0]) | (A[0] & CIN) | (B[0] & CIN))))))
    );

    // Bit 3 sum XORs A[3] and B[3] with COUT.
    check_sum_bit3_uses_cout: assert property (
        @(posedge clk)
        S[3] == (A[3] ^ B[3] ^ COUT)
    );

    // Lower outputs depend only on A[2:0], B[2:0], and CIN.
    check_lower_outputs_stable_when_lower_inputs_stable: assert property (
        @(posedge clk)
        ($stable(A[2:0]) && $stable(B[2:0]) && $stable(CIN)) |-> $stable({COUT, S[2:0]})
    );

    // The MSB sum stays stable when A[3], B[3], and COUT stay stable.
    check_msb_sum_stable_when_its_inputs_stable: assert property (
        @(posedge clk)
        ($stable(A[3]) && $stable(B[3]) && $stable(COUT)) |-> $stable(S[3])
    );

endmodule