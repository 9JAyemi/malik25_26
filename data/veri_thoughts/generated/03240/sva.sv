module arithmetic_module_sva(
    input logic [7:0] A,
    input logic [7:0] B,
    input logic [15:0] C
);

    // Low byte matches the addition result modulo 256.
    check_sum_low_byte: assert property (
        @($global_clock) C[7:0] == ((A + B) & 8'hFF)
    );

    // Upper byte stays zero after the assignment to C.
    check_sum_high_byte_zero: assert property (
        @($global_clock) C[15:8] == 8'h00
    );

    // When A is zero, C passes B through in the low byte.
    check_a_zero_passthrough: assert property (
        @($global_clock) (A == 8'h00) |-> (C == {8'h00, B})
    );

    // When B is zero, C passes A through in the low byte.
    check_b_zero_passthrough: assert property (
        @($global_clock) (B == 8'h00) |-> (C == {8'h00, A})
    );

    // FF + 01 wraps in the low byte.
    check_ff_plus_01_wraps: assert property (
        @($global_clock) ((A == 8'hFF) && (B == 8'h01)) |-> (C == 16'h0000)
    );

    // FF + FF produces FE in the low byte.
    check_ff_plus_ff_truncates: assert property (
        @($global_clock) ((A == 8'hFF) && (B == 8'hFF)) |-> (C == 16'h00FE)
    );

endmodule