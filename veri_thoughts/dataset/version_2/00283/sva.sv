module sky130_fd_sc_lp__dfxtp_sva (
    input logic D,
    input logic Q,
    input logic CLK,
    input logic VPB,
    input logic VPWR,
    input logic VGND,
    input logic VNB
);

    // Q reflects the D value sampled on the previous rising edge.
    check_q_tracks_previous_d: assert property (
        @(posedge CLK) !$initstate |-> (Q == $past(D))
    );

    // A sampled high D drives Q high on the next rising edge.
    check_high_capture: assert property (
        @(posedge CLK) D |=> Q
    );

    // A sampled low D drives Q low on the next rising edge.
    check_low_capture: assert property (
        @(posedge CLK) !D |=> !Q
    );

    // A change in sampled D appears as a change in Q one cycle later.
    check_d_change_propagates: assert property (
        @(posedge CLK) (!$initstate && (D != $past(D))) |=> (Q != $past(Q))
    );

    // An unchanged sampled D keeps Q unchanged one cycle later.
    check_d_stable_keeps_q_stable: assert property (
        @(posedge CLK) (!$initstate && (D == $past(D))) |=> (Q == $past(Q))
    );

endmodule