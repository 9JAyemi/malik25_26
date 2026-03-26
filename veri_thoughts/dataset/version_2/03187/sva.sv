module adder_sva (
    input logic       clk,
    input logic [7:0] A,
    input logic [7:0] B,
    input logic [7:0] sum
);

    // DUT is combinational; clk is the sampling clock for these assertions.

    // Sum must match the 8-bit addition of A and B.
    check_byte_addition: assert property (
        @(posedge clk) sum == (A + B)
    );

    // Bit 0 must be A[0] xor B[0] because the first carry-in is tied low.
    check_lsb_xor: assert property (
        @(posedge clk) sum[0] == (A[0] ^ B[0])
    );

    // The low nibble must match 4-bit addition of the low nibbles.
    check_low_nibble_addition: assert property (
        @(posedge clk) sum[3:0] == (A[3:0] + B[3:0])
    );

    // Adding zero on B must pass A through unchanged.
    check_b_zero_passthrough: assert property (
        @(posedge clk) (B == 8'h00) |-> (sum == A)
    );

    // Adding zero on A must pass B through unchanged.
    check_a_zero_passthrough: assert property (
        @(posedge clk) (A == 8'h00) |-> (sum == B)
    );

    // Zero plus zero must produce zero.
    check_zero_plus_zero: assert property (
        @(posedge clk) ((A == 8'h00) && (B == 8'h00)) |-> (sum == 8'h00)
    );

    // 0xFF plus 0x01 must wrap to 0x00 on the 8-bit output.
    check_ff_plus_one_wraps: assert property (
        @(posedge clk) ((A == 8'hFF) && (B == 8'h01)) |-> (sum == 8'h00)
    );

    // 0xFF plus 0xFF must produce 0xFE on the 8-bit output.
    check_ff_plus_ff: assert property (
        @(posedge clk) ((A == 8'hFF) && (B == 8'hFF)) |-> (sum == 8'hFE)
    );

    // Stable inputs must keep the sampled sum stable.
    check_stable_inputs_stable_sum: assert property (
        @(posedge clk) ($stable(A) && $stable(B)) |-> $stable(sum)
    );

endmodule