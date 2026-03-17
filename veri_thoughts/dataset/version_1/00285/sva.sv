module four_bit_adder_sva (
    input logic       clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic       Cin,
    input logic [3:0] S,
    input logic       Cout
);

    function automatic logic sum3 (
        input logic x,
        input logic y,
        input logic z
    );
        sum3 = x ^ y ^ z;
    endfunction

    function automatic logic carry3 (
        input logic x,
        input logic y,
        input logic z
    );
        carry3 = (x & y) | (x & z) | (y & z);
    endfunction

    // Combined output matches 4-bit addition with carry-in.
    check_total_sum: assert property (
        @(posedge clk) {Cout, S} == ({1'b0, A} + {1'b0, B} + {4'b0000, Cin})
    );

    // Bit 0 sum matches the first full-adder XOR behavior.
    check_bit0_sum: assert property (
        @(posedge clk) S[0] == sum3(A[0], B[0], Cin)
    );

    // Bit 1 sum uses the carry from bit 0.
    check_bit1_sum: assert property (
        @(posedge clk) S[1] == sum3(A[1], B[1], carry3(A[0], B[0], Cin))
    );

    // Bit 2 sum uses the carry from bit 1.
    check_bit2_sum: assert property (
        @(posedge clk) S[2] == sum3(
            A[2],
            B[2],
            carry3(A[1], B[1], carry3(A[0], B[0], Cin))
        )
    );

    // Bit 3 sum uses the carry from bit 2.
    check_bit3_sum: assert property (
        @(posedge clk) S[3] == sum3(
            A[3],
            B[3],
            carry3(A[2], B[2], carry3(A[1], B[1], carry3(A[0], B[0], Cin)))
        )
    );

    // Final carry-out matches the last full-adder carry logic.
    check_final_carry: assert property (
        @(posedge clk) Cout == carry3(
            A[3],
            B[3],
            carry3(A[2], B[2], carry3(A[1], B[1], carry3(A[0], B[0], Cin)))
        )
    );

endmodule