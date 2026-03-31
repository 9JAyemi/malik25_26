```systemverilog
module system_axi_ethernetlite_0_0_synchronizer_ff_9_sva (
    input logic phy_tx_clk,
    input logic [0:0] in0,
    input logic [0:0] AS,
    input logic out
);
    // Q_reg is updated on the rising edge of phy_tx_clk
    update_Q_reg: assert property (
        @(posedge phy_tx_clk) disable iff (!phy_tx_clk) out |-> Q_reg == out
    );

    // AS is updated on the rising edge of phy_tx_clk
    update_AS: assert property (
        @(posedge phy_tx_clk) disable iff (!phy_tx_clk) (in0 & ~Q_reg) |-> AS == (in0 & ~Q_reg)
    );

    // AS is always equal to (in0 & ~Q_reg)
    always_equal: assert property (
        @(posedge phy_tx_clk) disable iff (!phy_tx_clk) AS == (in0 & ~Q_reg)
    );

endmodule
```