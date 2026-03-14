module power_supply_converter_sva (
    input logic HI,
    input logic LO,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB,
    input logic CLK,
    input logic RST
);

    // On reset, outputs must be driven LOW.
    check_reset_outputs_low: assert property (
        @(posedge CLK) RST |-> (HI == 1'b0) && (LO == 1'b0)
    );

    // HI and LO are never both HIGH.
    check_outputs_mutex: assert property (
        @(posedge CLK) disable iff (RST) !(HI && LO)
    );

    // If HI is HIGH, LO must be LOW.
    check_hi_excludes_lo: assert property (
        @(posedge CLK) disable iff (RST) HI |-> !LO
    );

    // If LO is HIGH, HI must be LOW.
    check_lo_excludes_hi: assert property (
        @(posedge CLK) disable iff (RST) LO |-> !HI
    );

    // If previously not in reset and VPB > VNB, outputs must be HI=1, LO=0.
    map_prev_gt_to_hi: assert property (
        @(posedge CLK) disable iff (RST) ($past(!RST) && $past(VPB > VNB)) |-> (HI && !LO)
    );

    // If previously not in reset and VNB > VPB, outputs must be LO=1, HI=0.
    map_prev_lt_to_lo: assert property (
        @(posedge CLK) disable iff (RST) ($past(!RST) && $past(VNB > VPB)) |-> (LO && !HI)
    );

    // If previously not in reset and VPB == VNB, outputs must be HI=0, LO=0.
    map_prev_eq_to_zero: assert property (
        @(posedge CLK) disable iff (RST) ($past(!RST) && $past(VPB == VNB)) |-> (!HI && !LO)
    );

    // HI=1,LO=0 implies previously VPB > VNB.
    hi_implies_prev_gt: assert property (
        @(posedge CLK) disable iff (RST) (HI && !LO) |-> $past(VPB > VNB)
    );

    // LO=1,HI=0 implies previously VNB > VPB.
    lo_implies_prev_lt: assert property (
        @(posedge CLK) disable iff (RST) (LO && !HI) |-> $past(VNB > VPB)
    );

    // HI=0,LO=0 implies previously VPB == VNB or reset was asserted.
    zero_implies_prev_eq_or_reset: assert property (
        @(posedge CLK) disable iff (RST) (!HI && !LO) |-> ($past(VPB == VNB) || $past(RST))
    );

endmodule