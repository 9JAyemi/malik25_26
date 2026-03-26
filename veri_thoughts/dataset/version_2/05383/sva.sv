module pcie_7x_0_core_top_gtx_cpllpd_ovrd_sva (
    input logic i_ibufds_gte2,
    input logic o_cpllpd_ovrd,
    input logic o_cpllreset_ovrd
);

    // Initial values reflect the register initializations.
    check_initial_outputs: assert property (
        @(posedge i_ibufds_gte2)
        $initstate |-> (o_cpllpd_ovrd && !o_cpllreset_ovrd)
    );

    // The CPLL powerdown override stays high for 96 clocks, then deasserts.
    check_cpllpd_init_duration: assert property (
        @(posedge i_ibufds_gte2)
        $initstate |-> (o_cpllpd_ovrd)[*96] ##1 (!o_cpllpd_ovrd)
    );

    // Once the CPLL powerdown override goes low, it stays low.
    check_cpllpd_stays_low: assert property (
        @(posedge i_ibufds_gte2)
        !o_cpllpd_ovrd |=> !o_cpllpd_ovrd
    );

    // The CPLL reset override stays low for 120 clocks, pulses high for 8 clocks, then goes low.
    check_cpllreset_init_pulse: assert property (
        @(posedge i_ibufds_gte2)
        $initstate |-> (!o_cpllreset_ovrd)[*120] ##1 (o_cpllreset_ovrd)[*8] ##1 (!o_cpllreset_ovrd)
    );

    // The reset override rises 24 clocks after the powerdown override falls.
    check_cpllreset_delay_after_cpllpd_fall: assert property (
        @(posedge i_ibufds_gte2)
        (!$initstate && $fell(o_cpllpd_ovrd)) |-> (!o_cpllreset_ovrd)[*24] ##1 $rose(o_cpllreset_ovrd)
    );

    // Once the reset override rises, it remains high for 8 total clocks and then deasserts.
    check_cpllreset_pulse_width: assert property (
        @(posedge i_ibufds_gte2)
        (!$initstate && $rose(o_cpllreset_ovrd)) |=> (o_cpllreset_ovrd)[*7] ##1 (!o_cpllreset_ovrd)
    );

    // The two override outputs are never high at the same time.
    check_outputs_do_not_overlap: assert property (
        @(posedge i_ibufds_gte2)
        !(o_cpllpd_ovrd && o_cpllreset_ovrd)
    );

endmodule