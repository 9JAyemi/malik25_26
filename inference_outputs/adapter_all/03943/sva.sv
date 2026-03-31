module system_axi_ethernetlite_0_0_synchronizer_ff_9_sva (
    input logic clk,
    input logic AS,
    input logic out,
    input logic phy_tx_clk,
    input logic [0:0] in0
);
    // AS equals in0 & ~out delayed by one phy_tx_clk.
    check_as_definition: assert property (
        @(posedge phy_tx_clk) AS == (in0 & ~out)
    );

    // If in0 is 0, AS must be 0 on the next cycle.
    check_in0_zero_forces_as_zero: assert property (
        @(posedge phy_tx_clk) (in0 == 1'b0) |=> (AS == 1'b0)
    );

    // If out is 1, AS must be 0 on the next cycle.
    check_out_one_forces_as_zero: assert property (
        @(posedge phy_tx_clk) (out == 1'b1) |=> (AS == 1'b0)
    );

    // If in0 is 1 and out is 0, AS must be 1 on the next cycle.
    check_in0_one_out_zero_sets_as: assert property (
        @(posedge phy_tx_clk) (in0 == 1'b1 && out == 1'b0) |=> (AS == 1'b1)
    );

    // If AS is 1, then in0 must be 1 and out must be 0 in the same cycle.
    check_as_one_implies_inputs: assert property (
        @(posedge phy_tx_clk) (AS == 1'b1) |-> (in0 == 1'b1 && out == 1'b0)
    );

    // If AS is 0, then either in0 is 0 or out is 1 in the same cycle.
    check_as_zero_implies_inputs: assert property (
        @(posedge phy_tx_clk) (AS == 1'b0) |-> ((in0 == 1'b0) || (out == 1'b1))
    );

    // If in0 and out are stable, AS must be stable on the next cycle.
    check_stable_inputs_hold_as: assert property (
        @(posedge phy_tx_clk) $stable(in0) && $stable(out) |=> $stable(AS)
    );

    // If in0 toggles and out is stable, AS must toggle on the next cycle.
    check_in0_toggle_toggles_as: assert property (
        @(posedge phy_tx_clk) $changed(in0) && $stable(out) |=> $changed(AS)
    );

    // If out toggles and in0 is stable, AS must toggle on the next cycle.
    check_out_toggle_toggles_as: assert property (
        @(posedge phy_tx_clk) $changed(out) && $stable(in0) |=> $changed(AS)
    );

    // If in0 and out both toggle, AS must be stable on the next cycle.
    check_both_toggle_hold_as: assert property (
        @(posedge phy_tx_clk) $changed(in0) && $changed(out) |=> $stable(AS)
    );
endmodule