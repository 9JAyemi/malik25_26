module system_axi_ethernetlite_0_0_synchronizer_ff_9_sva (
    input logic [0:0] AS,
    input logic       out,
    input logic       phy_tx_clk,
    input logic [0:0] in0
);

    // AS must be low whenever in0 is low.
    check_as_low_when_in0_low: assert property (
        @(posedge phy_tx_clk) (in0 == 1'b0) |-> (AS == 1'b0)
    );

    // A high sampled out value forces AS low on the next cycle.
    check_next_as_low_after_out_high: assert property (
        @(posedge phy_tx_clk) out |-> ##1 (AS == 1'b0)
    );

    // A low sampled out value makes AS follow in0 on the next cycle.
    check_next_as_follows_in0_after_out_low: assert property (
        @(posedge phy_tx_clk) !out |-> ##1 (AS == in0)
    );

    // AS equals current in0 masked by the previously sampled out value.
    check_as_matches_delayed_out_mask: assert property (
        @(posedge phy_tx_clk) 1'b1 |-> ##1 (AS == (in0 & ~$past(out)))
    );

endmodule