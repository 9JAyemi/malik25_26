module clock_inverter_sva (
    input logic clk,
    input logic Y,
    input logic Y_internal
);
    // On each rising edge after the first sample, Y equals the previous value of Y_internal.
    check_y_tracks_prev_y_internal: assert property (
        @(posedge clk) $past(1'b1) |-> (Y == $past(Y_internal))
    );

    // Y_internal never changes after its initial assignment.
    check_y_internal_stable: assert property (
        @(posedge clk) $past(1'b1) |-> $stable(Y_internal)
    );

    // If Y changed since the last sample, its new value equals the previous Y_internal.
    check_y_change_implies_prev_y_internal: assert property (
        @(posedge clk) $changed(Y) |-> (Y == $past(Y_internal))
    );

    // If Y_internal is stable over a cycle, then Y is stable on the next cycle.
    check_y_stable_when_y_internal_stable: assert property (
        @(posedge clk) ($past(1'b1) && $stable(Y_internal)) |-> ##1 (Y == $past(Y))
    );
endmodule