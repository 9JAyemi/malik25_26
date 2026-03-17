module synchronizer_ff_15_sva (
    input logic out,
    input logic rd_rst_asreg_reg,
    input logic [0:0] in0,
    input logic s_axi_aclk
);

    // The flag is the combinational mismatch between in0 and out.
    check_flag_definition: assert property (
        @(posedge s_axi_aclk) rd_rst_asreg_reg === (in0[0] != out)
    );

    // A high mismatch flag clears the registered output on the next clock.
    check_mismatch_clears_out: assert property (
        @(posedge s_axi_aclk) rd_rst_asreg_reg |=> (out == 1'b0)
    );

    // With no mismatch, the registered output captures the current input.
    check_match_captures_input: assert property (
        @(posedge s_axi_aclk) !rd_rst_asreg_reg |=> (out === $past(in0[0]))
    );

    // Once out is low, this logic keeps it low on the next cycle.
    check_zero_state_sticky: assert property (
        @(posedge s_axi_aclk) (out == 1'b0) |=> (out == 1'b0)
    );

    // A high output stays high when the input is also high.
    check_high_holds_with_high_input: assert property (
        @(posedge s_axi_aclk) (out == 1'b1 && in0[0] == 1'b1) |=> (out == 1'b1)
    );

    // A high output clears when the input goes low.
    check_high_clears_with_low_input: assert property (
        @(posedge s_axi_aclk) (out == 1'b1 && in0[0] == 1'b0) |=> (out == 1'b0)
    );

endmodule