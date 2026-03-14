module BitShifting_sva (
    input logic CLK,
    input logic [31:0] a,
    input logic [4:0] n,
    input logic [31:0] b
);
    // When n==0, output passes through input a.
    check_passthrough_when_n_zero: assert property (
        @(posedge CLK) (n == 5'd0) |-> (b == a)
    );

    // When n>0, output equals a left-shifted by n.
    check_shift_when_n_positive: assert property (
        @(posedge CLK) (n > 5'd0) |-> (b == (a << n))
    );

    // When n>0, the lower n bits of b are zero after left shift.
    check_lower_bits_zero_after_shift: assert property (
        @(posedge CLK) (n > 5'd0) |-> ((b & (((32'h1 << n) - 32'h1))) == 32'h0)
    );

    // When n>0, bit b[n] equals a[0] after left shift.
    check_bit_n_equals_a0: assert property (
        @(posedge CLK) (n > 5'd0) |-> (b[n] == a[0])
    );

    // When n>0, MSB of b equals a[31-n].
    check_msb_matches_source_bit: assert property (
        @(posedge CLK) (n > 5'd0) |-> (b[31] == a[31 - n])
    );

    // If n hypothetically exceeded 31, b would be forced to zero per RTL branch.
    check_large_n_forces_zero: assert property (
        @(posedge CLK) (n > 5'd31) |-> (b == 32'h0)
    );

    // If a is zero, b is zero regardless of n.
    check_zero_input_produces_zero_output: assert property (
        @(posedge CLK) (a == 32'h0) |-> (b == 32'h0)
    );

    // If a is stable and n increments by 1 (and was <31), b shifts left by 1 from prior b.
    check_incremental_n_shifts_output: assert property (
        @(posedge CLK) ($past(a) === a) && ($past(n) < 5'd31) && (n == ($past(n) + 5'd1)) |-> (b == ($past(b) << 1))
    );

    // If a and n are stable, b remains stable (pure combinational function).
    check_stable_inputs_keep_output_stable: assert property (
        @(posedge CLK) $stable(a) && $stable(n) |-> $stable(b)
    );

    // For n==31, b equals {a[0], 31'b0}.
    check_shift_by_31_behavior: assert property (
        @(posedge CLK) (n == 5'd31) |-> (b == {a[0], 31'b0})
    );
endmodule