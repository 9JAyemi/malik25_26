module ripple_carry_adder_sva (
    input logic CLK,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [3:0] OUT
);
    // OUT must equal A + B modulo 16.
    check_sum_mod16: assert property (
        @(posedge CLK) OUT == (A + B)
    );

    // LSB is XOR of inputs (CIN=0).
    check_bit0_xor: assert property (
        @(posedge CLK) OUT[0] == (A[0] ^ B[0])
    );

    // Bit1 sum with carry from bit0.
    check_bit1_sum: assert property (
        @(posedge CLK) OUT[1] == ((A[1] ^ B[1]) ^ (A[0] & B[0]))
    );

    // Bit2 sum with carry from lower bits.
    check_bit2_sum: assert property (
        @(posedge CLK) OUT[2] == ((A[2] ^ B[2]) ^ ((A[1] & B[1]) | ((A[1] ^ B[1]) & (A[0] & B[0]))))
    );

    // Bit3 sum with carry from lower bits.
    check_bit3_sum: assert property (
        @(posedge CLK) OUT[3] == ((A[3] ^ B[3]) ^ ((A[2] & B[2]) | ((A[2] ^ B[2]) & ((A[1] & B[1]) | ((A[1] ^ B[1]) & (A[0] & B[0]))))))
    );

    // Adding zero on A passes B through.
    check_a_zero_passthru: assert property (
        @(posedge CLK) (A == 4'h0) |-> (OUT == B)
    );

    // Adding zero on B passes A through.
    check_b_zero_passthru: assert property (
        @(posedge CLK) (B == 4'h0) |-> (OUT == A)
    );

    // 15 + 1 wraps to 0 (carry-out ignored).
    check_wrap_15_plus_1: assert property (
        @(posedge CLK) ((A == 4'hF) && (B == 4'h1)) |-> (OUT == 4'h0)
    );

    // OUT is stable when A and B are stable across a cycle.
    check_stable_when_inputs_stable: assert property (
        @(posedge CLK) ($stable(A) && $stable(B)) |-> $stable(OUT)
    );

    // LSB toggles when A[0] changes and B[0] is stable.
    check_lsb_toggle_on_A0_change: assert property (
        @(posedge CLK) ($changed(A[0]) && $stable(B[0])) |-> $changed(OUT[0])
    );
endmodule