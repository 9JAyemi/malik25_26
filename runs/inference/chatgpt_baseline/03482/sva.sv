module TLU_assertions (
    input logic EN,
    input logic SE,
    input logic CK,
    input logic Q
);

    // Q captures SE on an enabled clock edge.
    check_capture_when_enabled: assert property (
        @(posedge CK) EN |=> (Q == $past(SE))
    );

    // Q holds its previous value when EN is low.
    check_hold_when_disabled: assert property (
        @(posedge CK) !EN |=> (Q == $past(Q))
    );

    // Enabling with different data causes Q to change.
    check_enabled_new_data_updates_q: assert property (
        @(posedge CK) EN && (SE != Q) |=> $changed(Q)
    );

    // Enabling with the same data leaves Q unchanged.
    check_enabled_same_data_keeps_q: assert property (
        @(posedge CK) EN && (SE == Q) |=> !$changed(Q)
    );

endmodule