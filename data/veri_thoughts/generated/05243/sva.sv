module dff_sky130_fd_sc_ls_sva (
    input logic Q,
    input logic CLK,
    input logic D,
    input logic DE
);

    // When enabled, Q reflects the D sampled on the previous rising edge.
    check_enabled_loads_d: assert property (
        @(posedge CLK) !$initstate && $past(DE) |-> (Q == $past(D))
    );

    // When disabled, Q holds its previous value across clock cycles.
    check_disabled_holds_q: assert property (
        @(posedge CLK) !$initstate && !$past(DE) |-> (Q == $past(Q))
    );

    // Any observed change in Q must come from an enabled previous clock edge.
    check_q_changes_only_when_enabled: assert property (
        @(posedge CLK) !$initstate && (Q != $past(Q)) |-> $past(DE)
    );

    // Enabled data different from the old Q must cause Q to change.
    check_different_enabled_data_changes_q: assert property (
        @(posedge CLK) !$initstate && $past(DE) && ($past(D) != $past(Q)) |-> (Q != $past(Q))
    );

    // Enabled data equal to the old Q must leave Q unchanged.
    check_same_enabled_data_keeps_q: assert property (
        @(posedge CLK) !$initstate && $past(DE) && ($past(D) == $past(Q)) |-> (Q == $past(Q))
    );

endmodule