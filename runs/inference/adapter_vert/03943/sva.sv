property SyncIneotid; @(posedge phy_tx_clk) (in0) |-> (Q_reg == out) ;endproperty 
 
 property SyncCheckeotid; @(posedge phy_tx_clk) (in0) &&  (  ! (in0 & ~Q_reg)  ) |->  (AS == 1'b1)  ;endproperty 
 
 property SyncCheckeotid; @(posedge phy_tx_clk) (in0) &&  (  (in0 & ~Q_reg)  ) |->  (AS == 1'b0)  ;endproperty 
 