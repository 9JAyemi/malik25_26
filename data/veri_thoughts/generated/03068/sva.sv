module my_module_assertions (
    input logic Q,
    input logic CLK,
    input logic D,
    input logic DE,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB
);

    // When enabled, the next sampled Q equals the captured D.
    check_capture_when_enabled: assert property (
        @(posedge CLK) DE |=> (Q == $past(D))
    );

    // When disabled, Q holds its previous sampled value.
    check_hold_when_disabled: assert property (
        @(posedge CLK) !DE |=> (Q == $past(Q))
    );

    // Any observed Q change requires DE high on the prior clock.
    check_change_requires_enable: assert property (
        @(posedge CLK) 1'b1 |=> ((Q != $past(Q)) |-> $past(DE))
    );

    // Any observed Q change matches the prior sampled D.
    check_change_matches_captured_d: assert property (
        @(posedge CLK) 1'b1 |=> ((Q != $past(Q)) |-> (Q == $past(D)))
    );

    // If enabled data already matches Q, Q stays unchanged.
    check_same_data_keeps_q: assert property (
        @(posedge CLK) DE && (D == Q) |=> (Q == $past(Q))
    );

    // If enabled data differs from Q, Q updates to that data.
    check_new_data_updates_q: assert property (
        @(posedge CLK) DE && (D != Q) |=> ((Q == $past(D)) && (Q != $past(Q)))
    );

endmodule