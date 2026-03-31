module ripple_carry_adder_sva (
    input logic clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [3:0] SUM
);

    // SUM[0] matches the first full adder with zero carry-in.
    check_sum_bit0: assert property (
        @(posedge clk) SUM[0] == (A[0] ^ B[0])
    );

    // SUM[1] matches the second stage using the bit-0 carry.
    check_sum_bit1: assert property (
        @(posedge clk) SUM[1] == (A[1] ^ B[1] ^ (A[0] & B[0]))
    );

    // SUM[2] matches the third stage using the propagated carry.
    check_sum_bit2: assert property (
        @(posedge clk)
        SUM[2] == (A[2] ^ B[2] ^
                   ((A[1] & B[1]) | ((A[0] & B[0]) & (A[1] ^ B[1]))))
    );

    // SUM[3] matches the fourth stage using the propagated carry.
    check_sum_bit3: assert property (
        @(posedge clk)
        SUM[3] == (A[3] ^ B[3] ^
                   ((A[2] & B[2]) |
                    (((A[1] & B[1]) | ((A[0] & B[0]) & (A[1] ^ B[1]))) &
                     (A[2] ^ B[2]))))
    );

    // SUM matches 4-bit addition with overflow discarded.
    check_sum_matches_addition: assert property (
        @(posedge clk) SUM == (A + B)
    );

endmodule