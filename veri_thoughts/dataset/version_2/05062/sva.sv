module pre_decoder_sva (
    input logic [5:0] addr_i,
    input logic pre_dec_o,
    input logic pre_dec_err_o
);

    // DUT is combinational, so properties are sampled on the formal global clock.

    // Mapped clock-domain #0 addresses decode with no select and no error.
    check_clk_domain0_decode: assert property (
        @($global_clock)
        ((addr_i[5:2] == 4'h0) || (addr_i[5:2] == 4'h8) || (addr_i[5:2] == 4'ha))
        |-> ((pre_dec_o == 1'b0) && (pre_dec_err_o == 1'b0))
    );

    // Mapped clock-domain #1 addresses decode with select asserted and no error.
    check_clk_domain1_decode: assert property (
        @($global_clock)
        ((addr_i[5:2] >= 4'h1) && (addr_i[5:2] <= 4'h7))
        |-> ((pre_dec_o == 1'b1) && (pre_dec_err_o == 1'b0))
    );

    // Unmapped addresses decode as an error with no select asserted.
    check_unmapped_decode_error: assert property (
        @($global_clock)
        ((addr_i[5:2] == 4'h9) || ((addr_i[5:2] >= 4'hb) && (addr_i[5:2] <= 4'hf)))
        |-> ((pre_dec_o == 1'b0) && (pre_dec_err_o == 1'b1))
    );

    // pre_dec_o can only be high for clock-domain #1 address ranges.
    check_pre_dec_only_for_domain1: assert property (
        @($global_clock)
        (pre_dec_o == 1'b1)
        |-> (((addr_i[5:2] >= 4'h1) && (addr_i[5:2] <= 4'h7)) && (pre_dec_err_o == 1'b0))
    );

    // pre_dec_err_o can only be high for unmapped address ranges.
    check_error_only_for_unmapped: assert property (
        @($global_clock)
        (pre_dec_err_o == 1'b1)
        |-> (((addr_i[5:2] == 4'h9) || ((addr_i[5:2] >= 4'hb) && (addr_i[5:2] <= 4'hf))) &&
             (pre_dec_o == 1'b0))
    );

    // The no-select, no-error result only occurs for the explicit clock-domain #0 addresses.
    check_zero_decode_only_for_domain0: assert property (
        @($global_clock)
        ((pre_dec_o == 1'b0) && (pre_dec_err_o == 1'b0))
        |-> ((addr_i[5:2] == 4'h0) || (addr_i[5:2] == 4'h8) || (addr_i[5:2] == 4'ha))
    );

    // The two outputs are never asserted together.
    check_outputs_mutually_exclusive: assert property (
        @($global_clock)
        !((pre_dec_o == 1'b1) && (pre_dec_err_o == 1'b1))
    );

    // Changes in addr_i[1:0] alone cannot change the outputs.
    check_outputs_depend_only_on_addr_high: assert property (
        @($global_clock)
        (!$initstate && (addr_i[5:2] == $past(addr_i[5:2])))
        |-> ((pre_dec_o == $past(pre_dec_o)) && (pre_dec_err_o == $past(pre_dec_err_o)))
    );

endmodule