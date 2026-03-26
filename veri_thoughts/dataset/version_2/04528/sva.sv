module sparc_tlu_zcmp64_sva (
    input logic        clk,
    input logic [63:0] in,
    input logic        zero
);

    // DUT is combinational with no reset; assertions are sampled on clk.

    // zero must assert when the input is exactly all zeros.
    check_zero_asserted_for_zero_input: assert property (
        @(posedge clk) (in === 64'b0) |-> (zero == 1'b1)
    );

    // zero must deassert for any input that is not exactly all zeros.
    check_zero_deasserted_for_nonzero_input: assert property (
        @(posedge clk) (in !== 64'b0) |-> (zero == 1'b0)
    );

    // If the sampled input is unchanged, the sampled output must also be unchanged.
    check_zero_stable_when_input_stable: assert property (
        @(posedge clk) $stable(in) |-> $stable(zero)
    );

endmodule