property SyncIneotid; @(posedge clk_in_1) (mdio_mdc) |-> (phy0_mdc) ;endproperty 
 
 property SyncOuteotid; @(posedge clk_in_1) (mdio_t) |-> (phy0_mdio_t) ;endproperty 
 
 property SyncOuteotid; @(posedge clk_in_1) (mdio_o) |-> (phy0_mdio_o) ;endproperty 
 
 property SyncIneotid; @(posedge clk_in_1) (mdio_mdc) |-> (phy1_mdc) ;endproperty 
 
 property SyncOuteotid; @(posedge clk_in_1) (mdio_t) |-> (phy1_mdio_t) ;endproperty 
 
 property SyncOuteotid; @(posedge clk_in_1) (mdio_o) |-> (phy1_mdio_o) ;endproperty 
 
 property SyncMatcheotid; @(posedge clk_in_1) (phy0_mdio_i) && (phy1_mdio_i) |-> (mdio_i) ;endproperty 
 