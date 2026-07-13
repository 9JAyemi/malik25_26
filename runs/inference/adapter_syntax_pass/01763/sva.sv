module mdio_1to2_sva (
    input logic mdio_mdc,
    input logic mdio_o,
    input logic mdio_t,
    input logic mdio_i,
    input logic phy0_mdc,
    input logic phy0_mdio_o,
    input logic phy0_mdio_t,
    input logic phy0_mdio_i,
    input logic phy1_mdc,
    input logic phy1_mdio_o,
    input logic phy1_mdio_t,
    input logic phy1_mdio_i
);

    // phy0_mdc is a direct copy of mdio_mdc.
    check_phy0_mdc_passthrough: assert property (
        @($global_clock) phy0_mdc == mdio_mdc
    );

    // phy1_mdc is a direct copy of mdio_mdc.
    check_phy1_mdc_passthrough: assert property (
        @($global_clock) phy1_mdc == mdio_mdc
    );

    // phy0_mdio_o is a direct copy of mdio_o.
    check_phy0_mdio_o_passthrough: assert property (
        @($global_clock) phy0_mdio_o == mdio_o
    );

    // phy1_mdio_o is a direct copy of mdio_o.
    check_phy1_mdio_o_passthrough: assert property (
        @($global_clock) phy1_mdio_o == mdio_o
    );

    // phy0_mdio_t is a direct copy of mdio_t.
    check_phy0_mdio_t_passthrough: assert property (
        @($global_clock) phy0_mdio_t == mdio_t
    );

    // phy1_mdio_t is a direct copy of mdio_t.
    check_phy1_mdio_t_passthrough: assert property (
        @($global_clock) phy1_mdio_t == mdio_t
    );

    // mdio_i is the AND of both PHY MDIO inputs.
    check_mdio_i_and_of_inputs: assert property (
        @($global_clock) mdio_i == (phy0_mdio_i & phy1_mdio_i)
    );

    // mdio_i matches the direct input to the AND gate.
    check_mdio_i_matches_direct_inputs: assert property (
        @($global_clock) mdio_i == (phy0_mdio_i & phy1_mdio_i)
    );

endmodule