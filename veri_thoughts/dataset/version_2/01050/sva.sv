module my_module_sva (
    input logic Ar,
    input logic Aa,
    input logic Br,
    input logic Ba
);
    // No clock/reset in RTL; combinational logic; assertions use $global_clock.
    // Behavior: Aa = Ar & Ba; Br = !Aa.

    // Aa must equal Ar & Ba.
    check_Aa_is_and: assert property (
        @(posedge $global_clock) Aa == (Ar & Ba)
    );

    // Br must be the logical negation of Aa.
    check_Br_is_not_Aa: assert property (
        @(posedge $global_clock) Br == !Aa
    );

    // Aa and Br are strict complements (never equal).
    check_outputs_complement: assert property (
        @(posedge $global_clock) (Aa ^ Br) == 1'b1
    );

    // If Aa is HIGH, both Ar and Ba must be HIGH.
    check_Aa_high_requires_inputs_high: assert property (
        @(posedge $global_clock) Aa |-> (Ar && Ba)
    );

    // If Ba is LOW, Aa must be LOW and Br must be HIGH.
    check_Ba_low_forces_outputs: assert property (
        @(posedge $global_clock) (Ba == 1'b0) |-> ((Aa == 1'b0) && (Br == 1'b1))
    );

    // If Ar is LOW, Aa must be LOW and Br must be HIGH.
    check_Ar_low_forces_outputs: assert property (
        @(posedge $global_clock) (Ar == 1'b0) |-> ((Aa == 1'b0) && (Br == 1'b1))
    );

    // If both Ar and Ba are HIGH, Aa must be HIGH and Br must be LOW.
    check_both_inputs_high: assert property (
        @(posedge $global_clock) (Ar && Ba) |-> ((Aa == 1'b1) && (Br == 1'b0))
    );

    // If Br is HIGH, at least one of Ar or Ba must be LOW.
    check_Br_high_implies_not_both_inputs_high: assert property (
        @(posedge $global_clock) (Br == 1'b1) |-> (!Ar || !Ba)
    );

    // If Br is LOW, both Ar and Ba must be HIGH.
    check_Br_low_implies_both_inputs_high: assert property (
        @(posedge $global_clock) (Br == 1'b0) |-> (Ar && Ba)
    );

    // Aa and Br can never both be HIGH in the same cycle.
    check_no_both_outputs_high: assert property (
        @(posedge $global_clock) !(Aa && Br)
    );
endmodule