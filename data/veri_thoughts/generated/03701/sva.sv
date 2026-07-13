module aurora_201_CHBOND_COUNT_DEC_sva #(
    parameter logic [5:0] CHANNEL_BOND_LOAD_CODE = 6'b100111
) (
    input logic [5:0] RX_STATUS,
    input logic       CHANNEL_BOND_LOAD,
    input logic       USER_CLK
);

    // CHANNEL_BOND_LOAD asserts one cycle after RX_STATUS matches the load code.
    check_load_asserts_on_match: assert property (
        @(posedge USER_CLK)
        (RX_STATUS == CHANNEL_BOND_LOAD_CODE) |=> CHANNEL_BOND_LOAD
    );

    // CHANNEL_BOND_LOAD deasserts one cycle after RX_STATUS does not match the load code.
    check_load_deasserts_on_mismatch: assert property (
        @(posedge USER_CLK)
        (RX_STATUS != CHANNEL_BOND_LOAD_CODE) |=> !CHANNEL_BOND_LOAD
    );

    // CHANNEL_BOND_LOAD is the registered decode of RX_STATUS from the prior clock.
    check_registered_decode: assert property (
        @(posedge USER_CLK)
        1'b1 |=> (CHANNEL_BOND_LOAD == ($past(RX_STATUS) == CHANNEL_BOND_LOAD_CODE))
    );

    // A rising CHANNEL_BOND_LOAD reflects a prior-cycle code match.
    check_load_rise_requires_prior_match: assert property (
        @(posedge USER_CLK)
        1'b1 |=> ($rose(CHANNEL_BOND_LOAD) |-> ($past(RX_STATUS) == CHANNEL_BOND_LOAD_CODE))
    );

    // A falling CHANNEL_BOND_LOAD reflects a prior-cycle code mismatch.
    check_load_fall_requires_prior_mismatch: assert property (
        @(posedge USER_CLK)
        1'b1 |=> ($fell(CHANNEL_BOND_LOAD) |-> ($past(RX_STATUS) != CHANNEL_BOND_LOAD_CODE))
    );

endmodule