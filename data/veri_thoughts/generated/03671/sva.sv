module counter_sva (
    input logic       CLK,
    input logic       RST,
    input logic       EN,
    input logic [3:0] OUT
);

    // A sampled low reset clears OUT by the next clock.
    check_reset_clears_out: assert property (
        @(posedge CLK) (!RST) |=> (OUT == 4'd0)
    );

    // On reset deassertion, the sampled counter value starts from zero.
    check_release_reset_starts_from_zero: assert property (
        @(posedge CLK) $rose(RST) |-> (OUT == 4'd0)
    );

    // When enabled, the counter increments by one on the next clock.
    check_increment_when_enabled: assert property (
        @(posedge CLK) disable iff (!RST)
        EN |=> (OUT == ($past(OUT) + 4'd1))
    );

    // When disabled, the counter holds its value on the next clock.
    check_hold_when_disabled: assert property (
        @(posedge CLK) disable iff (!RST)
        !EN |=> (OUT == $past(OUT))
    );

    // When enabled at 15, the 4-bit counter wraps to zero.
    check_wrap_from_max: assert property (
        @(posedge CLK) disable iff (!RST)
        (EN && (OUT == 4'hF)) |=> (OUT == 4'h0)
    );

endmodule