```systemverilog
module mdio_1to2_sva
    (input logic mdio_mdc,
     input logic mdio_o,
     input logic mdio_t,
     input logic mdio_i,

     input logic phy0_mdio_i,
     input logic phy1_mdio_i
     );

    // MDC is the same for both PHYs
    mdc_same: assert property (
        @(posedge mdio_mdc) $stable(mdio_mdc) |-> phy0_mdc == mdio_mdc && phy1_mdc == mdio_mdc
    );

    // MDIO_T is the same for both PHYs
    mdio_t_same: assert property (
        @(posedge mdio_mdc) $stable(mdio_t) |-> phy0_mdio_t == mdio_t && phy1_mdio_t == mdio_t
    );

    // MDIO_O is the same for both PHYs
    mdio_o_same: assert property (
        @(posedge mdio_mdc) $stable(mdio_o) |-> phy0_mdio_o == mdio_o && phy1_mdio_o == mdio_o
    );

    // MDIO_I is the AND of both PHYs' MDIO_I
    mdio_i_and: assert property (
        @(posedge mdio_mdc) $stable(phy0_mdio_i) && $stable(phy1_mdio_i) |-> mdio_i == (phy0_mdio_i & phy1_mdio_i)
    );

endmodule
```