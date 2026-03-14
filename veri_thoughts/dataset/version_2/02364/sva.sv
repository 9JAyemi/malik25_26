module bw_ioslave_dl_sva (
    input logic dqs_in,
    input logic [4:0] lpf_out,
    input logic se,
    input logic si,
    input logic strobe,
    input logic dqs_out,
    input logic so
);
    // Clocks: posedge dqs_in, posedge strobe; no reset in RTL.
    // Sequential logic: 5-stage delay line on dqs_in; so is registered on strobe when se=1.

    ///// dqs_in delay line behavior /////
    // dqs_out equals dqs_in delayed by 5 posedges of dqs_in.
    check_dqsout_delay_5: assert property (
        @(posedge dqs_in) 1'b1 |-> ##5 (dqs_out == $past(dqs_in,5))
    );

    // An input edge propagates to an output edge 5 cycles later.
    check_dqs_edge_propagation: assert property (
        @(posedge dqs_in) $changed(dqs_in) |-> ##5 $changed(dqs_out)
    );

    // If input does not change at a cycle, output does not change 5 cycles later.
    check_dqs_noedge_propagation: assert property (
        @(posedge dqs_in) !$changed(dqs_in) |-> ##5 !$changed(dqs_out)
    );

    // An output change implies the input changed 5 cycles earlier.
    check_dqsout_change_origin: assert property (
        @(posedge dqs_in) $changed(dqs_out) |-> ($past(dqs_in,5) != $past(dqs_in,6))
    );

    // If output does not change at a cycle, input did not change 5 cycles earlier.
    check_dqsout_nochange_origin: assert property (
        @(posedge dqs_in) !$changed(dqs_out) |-> ($past(dqs_in,5) == $past(dqs_in,6))
    );

    ///// strobe/so register behavior /////
    // When se==1 at strobe edge, so captures si.
    check_so_captures_si_when_se: assert property (
        @(posedge strobe) se |=> (so == $past(si))
    );

    // When se==0 at strobe edge, so holds its previous value.
    check_so_holds_when_se_low: assert property (
        @(posedge strobe) !se |=> (so == $past(so))
    );

    // A change on so can only occur when previous strobe had se==1.
    check_so_change_implies_se: assert property (
        @(posedge strobe) $changed(so) |-> $past(se)
    );

    // If previous strobe had se==1 and si differed from old so, so changes to that si.
    check_so_changes_when_si_differs: assert property (
        @(posedge strobe) se && (si != $past(so)) |=> ($changed(so) && (so == $past(si)))
    );

    // If previous strobe had se==1 and si equaled old so, so remains unchanged.
    check_so_stable_when_si_matches: assert property (
        @(posedge strobe) se && (si == $past(so)) |=> (!$changed(so) && (so == $past(so)))
    );

endmodule