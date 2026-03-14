module generate_output_signals_sva (
    input logic VPWR,
    input logic VGND,
    input logic VDD,
    input logic VSS,
    input logic VDD_VSS
);
    // VDD matches RTL function (sampled on VPWR rising edge).
    check_vdd_def_vpwr: assert property (
        @(posedge VPWR) VDD === (((VPWR == 1'b1) && (VGND == 1'b0)) ? 1'b1 : 1'b0)
    );

    // VDD matches RTL function (sampled on VGND rising edge).
    check_vdd_def_vgnd: assert property (
        @(posedge VGND) VDD === (((VPWR == 1'b1) && (VGND == 1'b0)) ? 1'b1 : 1'b0)
    );

    // VSS matches RTL function (sampled on VPWR rising edge).
    check_vss_def_vpwr: assert property (
        @(posedge VPWR) VSS === (((VGND == 1'b1) && (VPWR == 1'b0)) ? 1'b1 : 1'b0)
    );

    // VSS matches RTL function (sampled on VGND rising edge).
    check_vss_def_vgnd: assert property (
        @(posedge VGND) VSS === (((VGND == 1'b1) && (VPWR == 1'b0)) ? 1'b1 : 1'b0)
    );

    // VDD_VSS matches RTL function (sampled on VPWR rising edge).
    check_vdd_vss_def_vpwr: assert property (
        @(posedge VPWR) VDD_VSS === (((VDD == 1'b1) && (VSS == 1'b1)) ? 1'b1 : 1'b0)
    );

    // VDD_VSS matches RTL function (sampled on VGND rising edge).
    check_vdd_vss_def_vgnd: assert property (
        @(posedge VGND) VDD_VSS === (((VDD == 1'b1) && (VSS == 1'b1)) ? 1'b1 : 1'b0)
    );

    // If VDD is HIGH then VSS must be LOW (sampled on VPWR rising edge).
    vdd_high_implies_vss_low_vpwr: assert property (
        @(posedge VPWR) (VDD === 1'b1) |-> (VSS === 1'b0)
    );

    // If VDD is HIGH then VSS must be LOW (sampled on VGND rising edge).
    vdd_high_implies_vss_low_vgnd: assert property (
        @(posedge VGND) (VDD === 1'b1) |-> (VSS === 1'b0)
    );

    // If VSS is HIGH then VDD must be LOW (sampled on VPWR rising edge).
    vss_high_implies_vdd_low_vpwr: assert property (
        @(posedge VPWR) (VSS === 1'b1) |-> (VDD === 1'b0)
    );

    // If VSS is HIGH then VDD must be LOW (sampled on VGND rising edge).
    vss_high_implies_vdd_low_vgnd: assert property (
        @(posedge VGND) (VSS === 1'b1) |-> (VDD === 1'b0)
    );
endmodule