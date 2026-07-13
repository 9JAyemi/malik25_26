module sky130_fd_sc_ms__o21ai_sva (
    input logic A1,
    input logic A2,
    input logic B1,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB,
    input logic Y
);

    // No RTL clock or reset; assertions sample on the formal global clock.

    // Y must match the implemented combinational equation.
    check_output_matches_logic: assert property (
        @($global_clock)
        Y == ((A1 & A2 & B1) | (VPWR & VGND & VPB & VNB))
    );

    // The A1/A2/B1 product term forces Y high.
    check_data_term_forces_high: assert property (
        @($global_clock)
        (A1 & A2 & B1) |-> Y
    );

    // The VPWR/VGND/VPB/VNB product term forces Y high.
    check_power_term_forces_high: assert property (
        @($global_clock)
        (VPWR & VGND & VPB & VNB) |-> Y
    );

    // Y must be low when both product terms are low.
    check_both_terms_low_force_low: assert property (
        @($global_clock)
        (!(A1 & A2 & B1) && !(VPWR & VGND & VPB & VNB)) |-> !Y
    );

    // A high Y must come from at least one implemented product term.
    check_high_output_has_source: assert property (
        @($global_clock)
        Y |-> ((A1 & A2 & B1) || (VPWR & VGND & VPB & VNB))
    );

    // A low Y means the A1/A2/B1 product term is low.
    check_low_output_means_data_term_low: assert property (
        @($global_clock)
        !Y |-> !(A1 & A2 & B1)
    );

    // A low Y means the VPWR/VGND/VPB/VNB product term is low.
    check_low_output_means_power_term_low: assert property (
        @($global_clock)
        !Y |-> !(VPWR & VGND & VPB & VNB)
    );

    // If Y is high without the power term, the data term must be high.
    check_high_without_power_term_comes_from_data_term: assert property (
        @($global_clock)
        (Y && !(VPWR & VGND & VPB & VNB)) |-> (A1 & A2 & B1)
    );

    // If Y is high without the data term, the power term must be high.
    check_high_without_data_term_comes_from_power_term: assert property (
        @($global_clock)
        (Y && !(A1 & A2 & B1)) |-> (VPWR & VGND & VPB & VNB)
    );

endmodule