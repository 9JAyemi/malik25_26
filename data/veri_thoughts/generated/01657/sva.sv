module multiplier_sva (
    input logic CLK,          // sampling clock for assertions (design is combinational)
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [7:0] out
);
    // out must equal the combinational product of A and B.
    check_out_equals_product: assert property (
        @(posedge CLK) out == (A * B)
    );

    // If A is zero, out must be zero.
    check_zero_A_zero_out: assert property (
        @(posedge CLK) (A == 4'd0) |-> (out == 8'd0)
    );

    // If B is zero, out must be zero.
    check_zero_B_zero_out: assert property (
        @(posedge CLK) (B == 4'd0) |-> (out == 8'd0)
    );

    // If A is one, out must equal B.
    check_one_A_passthrough: assert property (
        @(posedge CLK) (A == 4'd1) |-> (out == B)
    );

    // If B is one, out must equal A.
    check_one_B_passthrough: assert property (
        @(posedge CLK) (B == 4'd1) |-> (out == A)
    );

    // The LSB of out equals the AND of input LSBs.
    check_lsb_matches_and: assert property (
        @(posedge CLK) out[0] == (A[0] & B[0])
    );

    // 15 x 15 must yield 225.
    check_15x15_corner: assert property (
        @(posedge CLK) ((A == 4'd15) && (B == 4'd15)) |-> (out == 8'd225)
    );

    // If A is 2, out equals B shifted left by 1.
    check_A_eq_2_shift1: assert property (
        @(posedge CLK) (A == 4'd2) |-> (out == (B << 1))
    );

    // If A is 4, out equals B shifted left by 2.
    check_A_eq_4_shift2: assert property (
        @(posedge CLK) (A == 4'd4) |-> (out == (B << 2))
    );

    // If A is 8, out equals B shifted left by 3.
    check_A_eq_8_shift3: assert property (
        @(posedge CLK) (A == 4'd8) |-> (out == (B << 3))
    );

    // If B is 2, out equals A shifted left by 1.
    check_B_eq_2_shift1: assert property (
        @(posedge CLK) (B == 4'd2) |-> (out == (A << 1))
    );

    // If B is 4, out equals A shifted left by 2.
    check_B_eq_4_shift2: assert property (
        @(posedge CLK) (B == 4'd4) |-> (out == (A << 2))
    );

    // If B is 8, out equals A shifted left by 3.
    check_B_eq_8_shift3: assert property (
        @(posedge CLK) (B == 4'd8) |-> (out == (A << 3))
    );
endmodule