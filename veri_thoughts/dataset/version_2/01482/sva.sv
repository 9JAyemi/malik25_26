module ripple_adder_sva (
    input logic CLK,
    input logic [3:0] a,
    input logic [3:0] b,
    input logic c
);

    // Compute ripple carry-out (cin=0) from a,b bits.
    function automatic logic carry4 (input logic [3:0] x, input logic [3:0] y);
        logic c1, c2, c3, c4;
        c1 = x[0] & y[0];
        c2 = (x[1] & y[1]) | ((x[1] ^ y[1]) & c1);
        c3 = (x[2] & y[2]) | ((x[2] ^ y[2]) & c2);
        c4 = (x[3] & y[3]) | ((x[3] ^ y[3]) & c3);
        return c4;
    endfunction

    // Compute carry-out of lower 3 bits (cin=0).
    function automatic logic carry3 (input logic [2:0] x, input logic [2:0] y);
        logic c1, c2, c3;
        c1 = x[0] & y[0];
        c2 = (x[1] & y[1]) | ((x[1] ^ y[1]) & c1);
        c3 = (x[2] & y[2]) | ((x[2] ^ y[2]) & c2);
        return c3;
    endfunction

    // Carry-out equals overflow bit of 5-bit sum {0,a}+{0,b}.
    check_c_matches_add_overflow: assert property (
        @(posedge CLK) c == ({1'b0, a} + {1'b0, b})[4]
    );

    // Carry-out matches explicit ripple-carry computation (cin=0).
    check_c_matches_ripple_chain: assert property (
        @(posedge CLK) c == carry4(a, b)
    );

    // No carry when either operand is zero.
    check_no_carry_when_operand_zero: assert property (
        @(posedge CLK) ((a == 4'b0000) || (b == 4'b0000)) |-> (c == 1'b0)
    );

    // No carry when both MSBs are 0.
    check_no_carry_when_msb00: assert property (
        @(posedge CLK) (!a[3] && !b[3]) |-> (c == 1'b0)
    );

    // Carry is 1 when both MSBs are 1.
    check_carry_when_msb11: assert property (
        @(posedge CLK) (a[3] && b[3]) |-> (c == 1'b1)
    );

    // If exactly one MSB is 1 and low 3-bit add carries, carry-out is 1.
    check_carry_one_msb_and_lower_carry: assert property (
        @(posedge CLK) ((a[3] ^ b[3]) && (carry3(a[2:0], b[2:0]) == 1'b1)) |-> (c == 1'b1)
    );

    // If exactly one MSB is 1 and low 3-bit add does not carry, carry-out is 0.
    check_no_carry_one_msb_no_lower_carry: assert property (
        @(posedge CLK) ((a[3] ^ b[3]) && (carry3(a[2:0], b[2:0]) == 1'b0)) |-> (c == 1'b0)
    );

endmodule