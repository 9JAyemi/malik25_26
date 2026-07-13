module system_axi_ethernetlite_0_0_synchronizer_ff_9_sva (
    input logic AS,
    input logic out,
    input logic phy_tx_clk,
    input logic [0:0] in0
);

// AS equals in0 AND NOT out on the next sampled clock.
    check_as_definition: assert property (
        @(posedge phy_tx_clk) 1'b1 |=> (AS == (in0 & ~out))
    );

// A high in0 must drive AS high on the next sampled clock.
    check_in0_high_sets_as: assert property (
        @(posedge phy_tx_clk) (in0 == 1'b1) |=> (AS == 1'b1)
    );

// A low in0 must drive AS low on the next sampled clock.
    check_in0_low_clears_as: assert property (
        @(posedge phy_tx_clk) (in0 == 1'b0) |=> (AS == 1'b0)
    );

// A high out must drive AS low on the next sampled clock.
    check_out_high_clears_as: assert property (
        @(posedge phy_tx_clk) (out == 1'b1) |=> (AS == 1'b0)
    );

// A low out must not force AS high when in0 is low.
    check_out_low_does_not_force_as_high: assert property (
        @(posedge phy_tx_clk) (out == 1'b0 && in0 == 1'b0) |=> (AS == 1'b0)
    );

endmodule
