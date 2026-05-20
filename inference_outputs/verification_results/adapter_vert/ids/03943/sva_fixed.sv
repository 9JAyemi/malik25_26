module system_axi_ethernetlite_0_0_synchronizer_ff_9_sva (
    input logic AS,
    input logic Q_reg,
    input logic in0,
    input logic out,
    input logic phy_tx_clk,
    input logic b0,
    input logic b1
);

property SyncIneotid; @(posedge phy_tx_clk) (in0) |-> (Q_reg == out) ;endproperty
assert property (SyncIneotid);

property SyncCheckeotid; @(posedge phy_tx_clk) (in0) &&  (  ! (in0 & ~Q_reg)  ) |->  (AS == 1'b1)  ;endproperty
assert property (SyncCheckeotid);

property SyncCheckeotid_2; @(posedge phy_tx_clk) (in0) &&  (  (in0 & ~Q_reg)  ) |->  (AS == 1'b0)  ;endproperty
assert property (SyncCheckeotid_2);

endmodule