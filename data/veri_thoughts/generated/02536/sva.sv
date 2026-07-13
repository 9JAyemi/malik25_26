module binary_op_sva (
    input logic clk,
    input logic [3:0] A,
    input logic [3:0] B
);
    // B equals the RTL's combinational function of A.
    check_b_function: assert property (
        @(posedge clk) B == ( (((A[1:0] + A[3:2]) % 3) == 0) ? (A >> 2) : (A + 4'd1) )
    );

    // When (A[1:0]+A[3:2])%3==0, B equals A >> 2.
    check_shift_path_value: assert property (
        @(posedge clk) (((A[1:0] + A[3:2]) % 3) == 0) |-> (B == (A >> 2))
    );

    // When (A[1:0]+A[3:2])%3==0, upper two bits of B are zero.
    check_shift_path_upper_zero: assert property (
        @(posedge clk) (((A[1:0] + A[3:2]) % 3) == 0) |-> (B[3:2] == 2'b00)
    );

    // When (A[1:0]+A[3:2])%3==0, lower two bits of B equal A[3:2].
    check_shift_path_lower_move: assert property (
        @(posedge clk) (((A[1:0] + A[3:2]) % 3) == 0) |-> (B[1:0] == A[3:2])
    );

    // When (A[1:0]+A[3:2])%3!=0, B equals A + 1 (mod 16).
    check_inc_path_value: assert property (
        @(posedge clk) (((A[1:0] + A[3:2]) % 3) != 0) |-> (B == (A + 4'd1))
    );

    // For A == 4'hF, the increment path wraps to zero.
    check_inc_wrap_at_max: assert property (
        @(posedge clk) (A == 4'hF) |-> (B == 4'h0)
    );
endmodule