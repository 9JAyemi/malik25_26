module ripple_carry_adder_sva (
    input logic clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic Cin,
    input logic [3:0] S,
    input logic Cout
);

    function automatic logic carry_out (
        input logic a,
        input logic b,
        input logic cin
    );
        carry_out = (a & b) | (a & cin) | (b & cin);
    endfunction

    // Full 5-bit result matches A + B + Cin.
    check_total_sum: assert property (
        @(posedge clk) disable iff (1'b0)
        {Cout, S} == ({1'b0, A} + {1'b0, B} + Cin)
    );

    // Sum bit 0 matches the first full-adder stage.
    check_sum_bit0: assert property (
        @(posedge clk) disable iff (1'b0)
        S[0] == (A[0] ^ B[0] ^ Cin)
    );

    // Sum bit 1 uses the carry from bit 0.
    check_sum_bit1: assert property (
        @(posedge clk) disable iff (1'b0)
        S[1] == (A[1] ^ B[1] ^ carry_out(A[0], B[0], Cin))
    );

    // Sum bit 2 uses the carry propagated through bit 1.
    check_sum_bit2: assert property (
        @(posedge clk) disable iff (1'b0)
        S[2] == (A[2] ^ B[2] ^ carry_out(A[1], B[1], carry_out(A[0], B[0], Cin)))
    );

    // Sum bit 3 uses the carry propagated through bit 2.
    check_sum_bit3: assert property (
        @(posedge clk) disable iff (1'b0)
        S[3] == (A[3] ^ B[3] ^ carry_out(A[2], B[2], carry_out(A[1], B[1], carry_out(A[0], B[0], Cin))))
    );

    // Final carry-out matches the ripple-carry chain.
    check_final_carry: assert property (
        @(posedge clk) disable iff (1'b0)
        Cout == carry_out(A[3], B[3], carry_out(A[2], B[2], carry_out(A[1], B[1], carry_out(A[0], B[0], Cin))))
    );

endmodule