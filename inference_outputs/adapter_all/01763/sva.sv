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

    // phy0_mdc mirrors mdio_mdc.
    check_phy0_mdc_passthrough: assert property (
        @(posedge mdio_mdc) phy0_mdc == mdio_mdc
    );

    // phy1_mdc mirrors mdio_mdc.
    check_phy1_mdc_passthrough: assert property (
        @(posedge mdio_mdc) phy1_mdc == mdio_mdc
    );

    // phy0_mdio_t mirrors mdio_t.
    check_phy0_mdio_t_passthrough: assert property (
        @(posedge mdio_t) phy0_mdio_t == mdio_t
    );

    // phy1_mdio_t mirrors mdio_t.
    check_phy1_mdio_t_passthrough: assert property (
        @(posedge mdio_t) phy1_mdio_t == mdio_t
    );

    // phy0_mdio_o mirrors mdio_o.
    check_phy0_mdio_o_passthrough: assert property (
        @(posedge mdio_o) phy0_mdio_o == mdio_o
    );

    // phy1_mdio_o mirrors mdio_o.
    check_phy1_mdio_o_passthrough: assert property (
        @(posedge mdio_o) phy1_mdio_o == mdio_o
    );

    // mdio_i is the AND of both PHY MDIO inputs.
    check_mdio_i_and: assert property (
        @(posedge mdio_i) mdio_i == (phy0_mdio_i & phy1_mdio_i)
    );

    // Both PHY MDIO inputs high drive mdio_i high.
    check_mdio_i_high_when_both_inputs_high: assert property (
        @(posedge mdio_i) (phy0_mdio_i & phy1_mdio_i) == 1'b1
    );

    // mdio_i low means at least one PHY MDIO input is low.
    check_mdio_i_low_when_any_input_low: assert property (
        @(posedge mdio_i) !(phy0_mdio_i & phy1_mdio_i) == 1'b1
    );

    // A high mdio_i requires both PHY MDIO inputs high.
    check_mdio_i_requires_both_inputs_high: assert property (
        @(posedge mdio_i) (phy0_mdio_i & phy1_mdio_i) == 1'b1
    );

endmodule