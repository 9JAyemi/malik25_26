module AND_GATE_sva #(
    parameter GSR = "ENABLED"
)(
    input logic D0,
    input logic D1,
    input logic RST,
    input logic ECLK,
    input logic SCLK,
    input logic Q
);

    // Reset forces Q low on the next clock.
    check_reset_clears_q: assert property (
        @(posedge SCLK)
        (RST == (GSR == "ENABLED")) |=> (Q == 1'b0)
    );

    // Enabled high with both inputs high sets Q.
    check_load_one_when_enabled: assert property (
        @(posedge SCLK) disable iff (RST == (GSR == "ENABLED"))
        ((ECLK == 1'b1) && (D0 == 1'b1) && (D1 == 1'b1)) |=> (Q == 1'b1)
    );

    // Enabled high with either input low clears Q.
    check_load_zero_when_enabled: assert property (
        @(posedge SCLK) disable iff (RST == (GSR == "ENABLED"))
        ((ECLK == 1'b1) && ((D0 == 1'b0) || (D1 == 1'b0))) |=> (Q == 1'b0)
    );

    // Disabled enable holds the registered value.
    check_hold_when_not_enabled: assert property (
        @(posedge SCLK) disable iff (RST == (GSR == "ENABLED"))
        (ECLK == 1'b0) |=> $stable(Q)
    );

    // Any Q change comes from a prior reset or enabled update.
    check_q_changes_only_after_reset_or_enable: assert property (
        @(posedge SCLK) disable iff ((RST == (GSR == "ENABLED")) || $initstate)
        $changed(Q) |-> ($past(RST == (GSR == "ENABLED")) || $past(ECLK == 1'b1))
    );

endmodule