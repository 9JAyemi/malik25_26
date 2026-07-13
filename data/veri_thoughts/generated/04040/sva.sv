module jcarrylookaheadadder_sva (
    input logic        clk,
    input logic [3:0]  Y,
    input logic        carryout,
    input logic [3:0]  A,
    input logic [3:0]  B,
    input logic        carryin
);

    // Y[0] is the XOR of the LSB inputs and carryin.
    check_y0_lsb_sum: assert property (
        @(posedge clk) Y[0] == (A[0] ^ B[0] ^ carryin)
    );

    // Y[1] uses the carry generated or propagated from bit 0.
    check_y1_sum_with_bit0_carry: assert property (
        @(posedge clk)
        Y[1] == (A[1] ^ B[1] ^ ((A[0] & B[0]) | ((A[0] ^ B[0]) & carryin)))
    );

    // Y[2] uses the carry generated or propagated through bits 1:0.
    check_y2_sum_with_bit1to0_carry: assert property (
        @(posedge clk)
        Y[2] == (A[2] ^ B[2] ^
                 ((A[1] & B[1]) |
                  ((A[1] ^ B[1]) &
                   ((A[0] & B[0]) | ((A[0] ^ B[0]) & carryin)))))
    );

    // Y[3] uses the carry generated or propagated through bits 2:0.
    check_y3_sum_with_bit2to0_carry: assert property (
        @(posedge clk)
        Y[3] == (A[3] ^ B[3] ^
                 ((A[2] & B[2]) |
                  ((A[2] ^ B[2]) &
                   ((A[1] & B[1]) |
                    ((A[1] ^ B[1]) &
                     ((A[0] & B[0]) | ((A[0] ^ B[0]) & carryin)))))))
    );

    // Y matches the 4-bit sum of A, B, and carryin.
    check_y_matches_4bit_sum: assert property (
        @(posedge clk) Y == (A + B + carryin)
    );

    // carryout matches the RTL's c[4] equation.
    check_carryout_equation: assert property (
        @(posedge clk)
        carryout == ((A[0] & B[0]) |
                     ((A[0] ^ B[0]) &
                      ((A[2] & B[2]) |
                       ((A[2] ^ B[2]) &
                        ((A[1] & B[1]) |
                         ((A[1] ^ B[1]) &
                          ((A[0] & B[0]) |
                           ((A[0] ^ B[0]) & carryin))))))))
    );

    // carryout is low when bit 0 is 00.
    check_carryout_low_when_bit0_is_zero_zero: assert property (
        @(posedge clk) ((A[0] == 1'b0) && (B[0] == 1'b0)) |-> (carryout == 1'b0)
    );

    // carryout is high when bit 0 is 11.
    check_carryout_high_when_bit0_is_one_one: assert property (
        @(posedge clk) ((A[0] == 1'b1) && (B[0] == 1'b1)) |-> (carryout == 1'b1)
    );

endmodule