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
    // Clock: mdio_mdc; Reset: none. Logic: combinational pass-through and AND on mdio_i.

    // phy0_mdc mirrors mdio_mdc.
    check_phy0_mdc_pass_through: assert property (
        @(posedge mdio_mdc) (phy0_mdc == mdio_mdc)
    );

    // phy1_mdc mirrors mdio_mdc.
    check_phy1_mdc_pass_through: assert property (
        @(posedge mdio_mdc) (phy1_mdc == mdio_mdc)
    );

    // phy0_mdio_t mirrors mdio_t.
    check_phy0_t_pass_through: assert property (
        @(posedge mdio_mdc) (phy0_mdio_t == mdio_t)
    );

    // phy1_mdio_t mirrors mdio_t.
    check_phy1_t_pass_through: assert property (
        @(posedge mdio_mdc) (phy1_mdio_t == mdio_t)
    );

    // phy0_mdio_o mirrors mdio_o.
    check_phy0_o_pass_through: assert property (
        @(posedge mdio_mdc) (phy0_mdio_o == mdio_o)
    );

    // phy1_mdio_o mirrors mdio_o.
    check_phy1_o_pass_through: assert property (
        @(posedge mdio_mdc) (phy1_mdio_o == mdio_o)
    );

    // mdio_i is the AND of phy0_mdio_i and phy1_mdio_i.
    check_mdio_i_and: assert property (
        @(posedge mdio_mdc) (mdio_i == (phy0_mdio_i & phy1_mdio_i))
    );

    // The two PHY MDC outputs are identical.
    check_mdc_consistency_between_phys: assert property (
        @(posedge mdio_mdc) (phy0_mdc == phy1_mdc)
    );

    // The two PHY MDIO_t outputs are identical.
    check_t_consistency_between_phys: assert property (
        @(posedge mdio_mdc) (phy0_mdio_t == phy1_mdio_t)
    );

    // The two PHY MDIO_o outputs are identical.
    check_o_consistency_between_phys: assert property (
        @(posedge mdio_mdc) (phy0_mdio_o == phy1_mdio_o)
    );

    // If either PHY MDIO input is 0, mdio_i must be 0.
    check_mdio_i_zero_if_any_zero: assert property (
        @(posedge mdio_mdc) ((!phy0_mdio_i) || (!phy1_mdio_i)) |-> (mdio_i == 1'b0)
    );

    // If both PHY MDIO inputs are 1, mdio_i must be 1.
    check_mdio_i_one_if_both_one: assert property (
        @(posedge mdio_mdc) (phy0_mdio_i && phy1_mdio_i) |-> (mdio_i == 1'b1)
    );
endmodule