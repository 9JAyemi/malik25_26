module system_axi_ethernetlite_0_0_synchronizer_ff_9_sva (
    input logic       AS,
    input logic [0:0] out,
    input logic       phy_tx_clk,
    input logic [0:0] in0
);

    // AS must equal in0 AND the previous-cycle out value.
    check_as_matches_previous_out: assert property (
        @(posedge phy_tx_clk) 1'b1 |=> (AS == (in0 & $past(out)))
    );

    // A low in0 must force AS low on the next clock.
    check_in0_low_forces_as_low: assert property (
        @(posedge phy_tx_clk) (in0 == 1'b0) |=> (AS == 1'b0)
    );

    // A high in0 must make AS follow the previous-cycle out value.
    check_in0_high_passes_previous_out: assert property (
        @(posedge phy_tx_clk) (in0 == 1'b1) |=> (AS == $past(out))
    );

    // A high AS requires both in0 and the previous-cycle out value to be high.
    check_as_high_requires_inputs: assert property (
        @(posedge phy_tx_clk) 1'b1 |=> ((AS == 1'b1) |-> ((in0 == 1'b1) && ($past(out) == 1'b1)))
    );

endmodule