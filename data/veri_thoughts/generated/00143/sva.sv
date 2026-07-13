module four_bit_adder_sva (
    input logic        clk,
    input logic [3:0]  A,
    input logic [3:0]  B,
    input logic        Cin,
    input logic [3:0]  Sum,
    input logic        Cout
);

    function automatic logic carry_bit(input logic x, input logic y, input logic z);
        carry_bit = (x & y) | (x & z) | (y & z);
    endfunction

    // Combined output must equal the 5-bit sum of A, B, and Cin.
    check_full_result: assert property (
        @(posedge clk) {Cout, Sum} == ({1'b0, A} + {1'b0, B} + Cin)
    );

    // Sum[0] must implement the least-significant full-adder sum bit.
    check_sum_bit0: assert property (
        @(posedge clk) Sum[0] == (A[0] ^ B[0] ^ Cin)
    );

    // Sum[1] must use the carry generated from bit 0.
    check_sum_bit1: assert property (
        @(posedge clk) Sum[1] == (A[1] ^ B[1] ^ carry_bit(A[0], B[0], Cin))
    );

    // Sum[2] must use the carry propagated through bits 0 and 1.
    check_sum_bit2: assert property (
        @(posedge clk) Sum[2] == (A[2] ^ B[2] ^ carry_bit(A[1], B[1], carry_bit(A[0], B[0], Cin)))
    );

    // Sum[3] must use the carry propagated through bits 0 to 2.
    check_sum_bit3: assert property (
        @(posedge clk) Sum[3] == (A[3] ^ B[3] ^ carry_bit(A[2], B[2], carry_bit(A[1], B[1], carry_bit(A[0], B[0], Cin))))
    );

    // Cout must be the final carry out of the most-significant bit.
    check_cout: assert property (
        @(posedge clk) Cout == carry_bit(A[3], B[3], carry_bit(A[2], B[2], carry_bit(A[1], B[1], carry_bit(A[0], B[0], Cin))))
    );

endmodule