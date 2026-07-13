module adder_mod_sva (
    input  logic        CLK,        // sampling clock for SVA
    input  logic [3:0]  A,
    input  logic [3:0]  B,
    input  logic [3:0]  sum,
    // Internal nets from adder_mod (bind to these for deeper checks)
    input  logic [3:0]  carry,
    input  logic [3:0]  full_sum
);
    // sum must equal internal full_sum bus.
    check_sum_matches_full_sum: assert property (
        @(posedge CLK) sum == full_sum
    );

    // fa0 implements A[0] + B[0] with cin=0.
    check_fa0_arith: assert property (
        @(posedge CLK) {carry[0], full_sum[0]} == (A[0] + B[0] + 1'b0)
    );

    // fa1 implements A[1] + B[1] with cin=carry[0].
    check_fa1_arith: assert property (
        @(posedge CLK) {carry[1], full_sum[1]} == (A[1] + B[1] + carry[0])
    );

    // fa2 implements A[2] + B[2] with cin=carry[1].
    check_fa2_arith: assert property (
        @(posedge CLK) {carry[2], full_sum[2]} == (A[2] + B[2] + carry[1])
    );

    // fa3 implements A[3] + B[3] with cin=carry[2].
    check_fa3_arith: assert property (
        @(posedge CLK) {carry[3], full_sum[3]} == (A[3] + B[3] + carry[2])
    );

    // Overall 5-bit result equals A + B (carry-out plus 4-bit sum).
    check_total_addition: assert property (
        @(posedge CLK) {carry[3], sum} == ({1'b0, A} + {1'b0, B})
    );

    // sum equals the truncated (LSB 4) of A + B.
    check_sum_truncation: assert property (
        @(posedge CLK) sum == (A + B)[3:0]
    );

    // Carry[0] is generate term for LSB adder (cin=0).
    check_carry0_generate: assert property (
        @(posedge CLK) carry[0] == (A[0] & B[0])
    );

    // Carry[1] is majority of A[1], B[1], carry[0].
    check_carry1_majority: assert property (
        @(posedge CLK) carry[1] == ((A[1] & B[1]) | (A[1] & carry[0]) | (B[1] & carry[0]))
    );

    // Carry[2] is majority of A[2], B[2], carry[1].
    check_carry2_majority: assert property (
        @(posedge CLK) carry[2] == ((A[2] & B[2]) | (A[2] & carry[1]) | (B[2] & carry[1]))
    );

    // Carry[3] is majority of A[3], B[3], carry[2].
    check_carry3_majority: assert property (
        @(posedge CLK) carry[3] == ((A[3] & B[3]) | (A[3] & carry[2]) | (B[3] & carry[2]))
    );

    // LSB sum bit is XOR of inputs (cin=0).
    check_sum0_xor: assert property (
        @(posedge CLK) full_sum[0] == (A[0] ^ B[0])
    );

    // Upper sum bits are XOR of inputs and incoming carry.
    check_sum_high_xor: assert property (
        @(posedge CLK) full_sum[3:1] == (A[3:1] ^ B[3:1] ^ carry[2:0])
    );
endmodule