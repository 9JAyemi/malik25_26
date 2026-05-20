module mdio_1to2_sva (
    input logic mdio_i,
    input logic mdio_mdc,
    input logic mdio_o,
    input logic mdio_t,
    input logic phy0_mdc,
    input logic phy0_mdio_i,
    input logic phy0_mdio_o,
    input logic phy0_mdio_t,
    input logic phy1_mdc,
    input logic phy1_mdio_i,
    input logic phy1_mdio_o,
    input logic phy1_mdio_t,
    input logic clk_in_1
);

property SyncIneotid; @(posedge clk_in_1) (mdio_mdc) |-> (phy0_mdc) ;endproperty
assert property (SyncIneotid);

property SyncOuteotid; @(posedge clk_in_1) (mdio_t) |-> (phy0_mdio_t) ;endproperty
assert property (SyncOuteotid);

property SyncOuteotid_2; @(posedge clk_in_1) (mdio_o) |-> (phy0_mdio_o) ;endproperty
assert property (SyncOuteotid_2);

property SyncIneotid_2; @(posedge clk_in_1) (mdio_mdc) |-> (phy1_mdc) ;endproperty
assert property (SyncIneotid_2);

property SyncOuteotid_3; @(posedge clk_in_1) (mdio_t) |-> (phy1_mdio_t) ;endproperty
assert property (SyncOuteotid_3);

property SyncOuteotid_4; @(posedge clk_in_1) (mdio_o) |-> (phy1_mdio_o) ;endproperty
assert property (SyncOuteotid_4);

property SyncMatcheotid; @(posedge clk_in_1) (phy0_mdio_i) && (phy1_mdio_i) |-> (mdio_i) ;endproperty
assert property (SyncMatcheotid);

endmodule