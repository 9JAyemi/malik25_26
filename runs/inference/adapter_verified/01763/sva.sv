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

// phy0 MDC mirrors mdio_mdc.
    check_phy0_mdc_passthrough: assert property (
        @(posedge mdio_mdc) phy0_mdc == mdio_mdc
    );

// phy0 MDIO T mirrors mdio_t.
    check_phy0_mdio_t_passthrough: assert property (
        @(posedge mdio_mdc) phy0_mdio_t == mdio_t
    );

// phy0 MDIO O mirrors mdio_o.
    check_phy0_mdio_o_passthrough: assert property (
        @(posedge mdio_mdc) phy0_mdio_o == mdio_o
    );

// phy1 MDC mirrors mdio_mdc.
    check_phy1_mdc_passthrough: assert property (
        @(posedge mdio_mdc) phy1_mdc == mdio_mdc
    );

// phy1 MDIO T mirrors mdio_t.
    check_phy1_mdio_t_passthrough: assert property (
        @(posedge mdio_mdc) phy1_mdio_t == mdio_t
    );

// phy1 MDIO O mirrors mdio_o.
    check_phy1_mdio_o_passthrough: assert property (
        @(posedge mdio_mdc) phy1_mdio_o == mdio_o
    );

// mdio_i is the AND of the two PHY MDIO inputs.
    check_mdio_i_is_and_of_phy_inputs: assert property (
        @(posedge mdio_mdc) mdio_i == (phy0_mdio_i & phy1_mdio_i)
    );

// A high mdio_i requires both PHY inputs to be high.
    check_mdio_i_high_requires_both_phis_high: assert property (
        @(posedge mdio_mdc) mdio_i |-> (phy0_mdio_i && phy1_mdio_i)
    );

// Both PHY inputs high drives mdio_i high.
    check_both_phis_high_drive_mdio_i_high: assert property (
        @(posedge mdio_mdc) (phy0_mdio_i && phy1_mdio_i) |-> mdio_i
    );

endmodule
