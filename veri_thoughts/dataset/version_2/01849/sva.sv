module decoder_using_case_sva (
    input logic clk,
    input logic [3:0] binary_in,
    input logic enable,
    input logic [15:0] decoder_out
);
    // When disabled, output must be all zeros.
    check_disabled_forces_zero: assert property (
        @(posedge clk) !enable |-> (decoder_out == 16'h0000)
    );

    // When enabled, output must equal 1 << binary_in.
    check_enabled_exact_decode: assert property (
        @(posedge clk) enable |-> (decoder_out == (16'h0001 << binary_in))
    );

    // When enabled, output must be strictly one-hot.
    check_onehot_when_enabled: assert property (
        @(posedge clk) enable |-> $onehot(decoder_out)
    );

    // Output is always zero or one-hot.
    check_onehot0_always: assert property (
        @(posedge clk) $onehot0(decoder_out)
    );

    // OR-reduction of output equals enable.
    check_or_reduce_matches_enable: assert property (
        @(posedge clk) ((|decoder_out) == enable)
    );

    // Non-zero output implies enable is HIGH.
    check_nonzero_implies_enabled: assert property (
        @(posedge clk) (decoder_out != 16'h0000) |-> enable
    );

    // When enabled, the selected bit by binary_in must be HIGH.
    check_selected_bit_high_when_enabled: assert property (
        @(posedge clk) enable |-> decoder_out[binary_in]
    );

    // When enabled, no bits other than the selected one may be set.
    check_no_other_bits_set_when_enabled: assert property (
        @(posedge clk) enable |-> ((decoder_out & ~(16'h0001 << binary_in)) == 16'h0000)
    );
endmodule