module adder_sva (
    input logic CLK,          // External clock for SVA sampling (DUT has no clock/reset)
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [4:0] sum
);
    // Sum equals A+B modulo 16 with zero MSB.
    check_sum_mod16: assert property (
        @(posedge CLK) sum == {1'b0, (A + B)[3:0]}
    );

    // MSB of sum is always zero.
    check_sum_msb_zero: assert property (
        @(posedge CLK) sum[4] == 1'b0
    );

    // Low nibble of sum equals low nibble of A+B.
    check_low_nibble_matches: assert property (
        @(posedge CLK) sum[3:0] == (A + B)[3:0]
    );

    // When no overflow, sum equals A+B exactly.
    check_no_overflow_result: assert property (
        @(posedge CLK) ((A + B) <= 5'd15) |-> (sum == (A + B))
    );

    // When overflow, sum wraps by subtracting 16.
    check_overflow_result: assert property (
        @(posedge CLK) ((A + B) >= 5'd16) |-> (sum == ((A + B) - 5'd16))
    );

    // Adding zero on A side passes B through (zero-extended).
    check_zero_A: assert property (
        @(posedge CLK) (A == 4'd0) |-> (sum == {1'b0, B})
    );

    // Adding zero on B side passes A through (zero-extended).
    check_zero_B: assert property (
        @(posedge CLK) (B == 4'd0) |-> (sum == {1'b0, A})
    );

    // Max plus max wraps to 14.
    check_max_plus_max: assert property (
        @(posedge CLK) ((A == 4'd15) && (B == 4'd15)) |-> (sum == 5'd14)
    );

    // 15 + 1 wraps to 0.
    check_wrap_15_plus_1: assert property (
        @(posedge CLK) ((A == 4'd15) && (B == 4'd1)) |-> (sum == 5'd0)
    );

    // 0 + 0 yields 0.
    check_zero_plus_zero: assert property (
        @(posedge CLK) ((A == 4'd0) && (B == 4'd0)) |-> (sum == 5'd0)
    );
endmodule