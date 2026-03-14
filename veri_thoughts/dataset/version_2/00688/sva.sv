module my_module_sva(
   input  logic               sgmii_refclk_p,
   input  logic               sgmii_refclk_n,
   input  logic [3:0]         sgmii_rxn,
   input  logic [3:0]         sgmii_rxp,
   input  logic               pl_btn,
   input  logic [3:0]         sgmii_txn,
   input  logic [3:0]         sgmii_txp,
   input  logic               mdio_mdc,
   input  logic [1:0]         pl_led,
   input  logic [1:0]         pl_pmod
);
   // sgmii_txn is the bitwise inverse of sgmii_rxn.
   check_txn_inverts_rxn: assert property (
      @(posedge sgmii_refclk_p) sgmii_txn === (sgmii_rxn ^ 4'b1111)
   );

   // sgmii_txp is the bitwise inverse of sgmii_rxp.
   check_txp_inverts_rxp: assert property (
      @(posedge sgmii_refclk_p) sgmii_txp === (sgmii_rxp ^ 4'b1111)
   );

   // sgmii_txn[0] equals inverse of sgmii_rxn[0].
   check_txn_b0_inverts_rxn_b0: assert property (
      @(posedge sgmii_refclk_p) sgmii_txn[0] === (~sgmii_rxn[0])
   );

   // sgmii_txn[3] equals inverse of sgmii_rxn[3].
   check_txn_b3_inverts_rxn_b3: assert property (
      @(posedge sgmii_refclk_p) sgmii_txn[3] === (~sgmii_rxn[3])
   );

   // sgmii_txp[0] equals inverse of sgmii_rxp[0].
   check_txp_b0_inverts_rxp_b0: assert property (
      @(posedge sgmii_refclk_p) sgmii_txp[0] === (~sgmii_rxp[0])
   );

   // sgmii_txp[3] equals inverse of sgmii_rxp[3].
   check_txp_b3_inverts_rxp_b3: assert property (
      @(posedge sgmii_refclk_p) sgmii_txp[3] === (~sgmii_rxp[3])
   );

   // mdio_mdc mirrors pl_btn.
   check_mdio_follows_btn: assert property (
      @(posedge sgmii_refclk_p) mdio_mdc === pl_btn
   );

   // pl_pmod[1] mirrors pl_btn.
   check_pmod1_follows_btn: assert property (
      @(posedge sgmii_refclk_p) pl_pmod[1] === pl_btn
   );

   // pl_pmod[1] matches mdio_mdc.
   check_pmod1_matches_mdio: assert property (
      @(posedge sgmii_refclk_p) pl_pmod[1] === mdio_mdc
   );
endmodule