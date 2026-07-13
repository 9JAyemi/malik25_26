module InputCell_sva (
    input logic InputPin,
    input logic FromPreviousBSCell,
    input logic CaptureDR,
    input logic ShiftDR,
    input logic TCK,
    input logic ToNextBSCell
);
    // Clock: TCK (posedge loads Latch, negedge updates ToNextBSCell). Reset: none. Logic: mixed (comb + seq).
    // Behavior: On posedge TCK with (CaptureDR|ShiftDR), selected input is latched; on next negedge, ToNextBSCell gets that latched value.

    // On negedge, when CaptureDR was 1 at prior posedge, drive sampled InputPin.
    check_capture_dr_updates_output: assert property (
        @(negedge TCK) $past(CaptureDR, 1, posedge TCK) |-> (ToNextBSCell == $past(InputPin, 1, posedge TCK))
    );

    // On negedge, when only ShiftDR was 1 at prior posedge, drive sampled FromPreviousBSCell.
    check_shift_dr_updates_output: assert property (
        @(negedge TCK) (!$past(CaptureDR, 1, posedge TCK) && $past(ShiftDR, 1, posedge TCK)) |-> (ToNextBSCell == $past(FromPreviousBSCell, 1, posedge TCK))
    );

    // On negedge, when both were 1 at prior posedge, CaptureDR has priority (use InputPin).
    check_priority_capture_over_shift: assert property (
        @(negedge TCK) ($past(CaptureDR, 1, posedge TCK) && $past(ShiftDR, 1, posedge TCK)) |-> (ToNextBSCell == $past(InputPin, 1, posedge TCK))
    );

    // On negedge, when neither enable was 1 at prior posedge, hold previous negedge value.
    check_hold_without_enable: assert property (
        @(negedge TCK) (!$past(CaptureDR, 1, posedge TCK) && !$past(ShiftDR, 1, posedge TCK)) |-> (ToNextBSCell == $past(ToNextBSCell, 1, negedge TCK))
    );

    // On negedge, any change in output must be preceded by CaptureDR or ShiftDR high at prior posedge.
    check_output_change_requires_enable: assert property (
        @(negedge TCK) (ToNextBSCell != $past(ToNextBSCell, 1, negedge TCK)) |-> $past(CaptureDR || ShiftDR, 1, posedge TCK)
    );

    // On negedge, when any enable was 1 at prior posedge, output equals selected input from that posedge.
    check_selected_input_function: assert property (
        @(negedge TCK) $past(CaptureDR || ShiftDR, 1, posedge TCK) |-> 
            (ToNextBSCell == ($past(CaptureDR, 1, posedge TCK) ? $past(InputPin, 1, posedge TCK) : $past(FromPreviousBSCell, 1, posedge TCK)))
    );

    // On negedge, if idle for two consecutive prior posedges, hold across two negedges.
    check_hold_across_two_idle_cycles: assert property (
        @(negedge TCK) (!$past(CaptureDR || ShiftDR, 1, posedge TCK) && !$past(CaptureDR || ShiftDR, 2, posedge TCK)) |-> 
            (ToNextBSCell == $past(ToNextBSCell, 2, negedge TCK))
    );
endmodule