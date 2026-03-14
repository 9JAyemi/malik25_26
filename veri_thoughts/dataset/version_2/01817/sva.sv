module diode_controller_sva (
    input logic DIODE,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB,
    input logic D1,
    input logic D2,
    input logic D3,
    input logic D4
);

    ///// Functional mapping checks /////
    // On DIODE rise, D1/D2 HIGH and D3/D4 LOW.
    map_forward_on_rise: assert property (
        @(posedge DIODE) disable iff (1'b0) (D1 === 1'b1) && (D2 === 1'b1) && (D3 === 1'b0) && (D4 === 1'b0)
    );

    // On DIODE fall, D1/D2 LOW and D3/D4 HIGH.
    map_reverse_on_fall: assert property (
        @(negedge DIODE) disable iff (1'b0) (D1 === 1'b0) && (D2 === 1'b0) && (D3 === 1'b1) && (D4 === 1'b1)
    );

    ///// Redundancy/consistency relations /////
    // D1 equals D2 on any DIODE edge.
    check_d1_eq_d2: assert property (
        @(posedge DIODE or negedge DIODE) disable iff (1'b0) (D1 === D2)
    );

    // D3 equals D4 on any DIODE edge.
    check_d3_eq_d4: assert property (
        @(posedge DIODE or negedge DIODE) disable iff (1'b0) (D3 === D4)
    );

    // D1 is the complement of D3 on any DIODE edge.
    check_d1_comp_d3: assert property (
        @(posedge DIODE or negedge DIODE) disable iff (1'b0) (D1 === ~D3)
    );

    // D2 is the complement of D4 on any DIODE edge.
    check_d2_comp_d4: assert property (
        @(posedge DIODE or negedge DIODE) disable iff (1'b0) (D2 === ~D4)
    );

    ///// Mutual exclusion for complementary pairs /////
    // D1 and D3 are never both HIGH.
    mutex_high_d1_d3: assert property (
        @(posedge DIODE or negedge DIODE) disable iff (1'b0) !((D1 === 1'b1) && (D3 === 1'b1))
    );

    // D1 and D3 are never both LOW.
    mutex_low_d1_d3: assert property (
        @(posedge DIODE or negedge DIODE) disable iff (1'b0) !((D1 === 1'b0) && (D3 === 1'b0))
    );

    // D2 and D4 are never both HIGH.
    mutex_high_d2_d4: assert property (
        @(posedge DIODE or negedge DIODE) disable iff (1'b0) !((D2 === 1'b1) && (D4 === 1'b1))
    );

    // D2 and D4 are never both LOW.
    mutex_low_d2_d4: assert property (
        @(posedge DIODE or negedge DIODE) disable iff (1'b0) !((D2 === 1'b0) && (D4 === 1'b0))
    );

endmodule