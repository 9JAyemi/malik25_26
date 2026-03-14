module up_counter_sva (
    input logic CLK,
    input logic RST,
    input logic EN,
    input logic [3:0] Q
);

    // On reset, Q becomes zero on the next cycle.
    reset_drives_zero_next: assert property (
        @(posedge CLK) RST |=> (Q == 4'd0)
    );

    // Reset overrides EN when both are asserted.
    reset_overrides_enable: assert property (
        @(posedge CLK) (RST && EN) |=> (Q == 4'd0)
    );

    // When EN=0 and not in reset, Q holds its value.
    hold_when_en_low: assert property (
        @(posedge CLK) disable iff (RST) (!EN) |=> $stable(Q)
    );

    // When EN=1 and not in reset, Q increments by 1 modulo 16.
    increment_when_en_high: assert property (
        @(posedge CLK) disable iff (RST) EN |=> (Q == $past(Q) + 4'd1)
    );

    // If previous Q was 0xF with EN=1, next Q wraps to 0.
    wrap_from_max_on_enable: assert property (
        @(posedge CLK) disable iff (RST) (EN && ($past(Q) == 4'hF)) |=> (Q == 4'd0)
    );

    // Q changes only if EN or RST was asserted in the prior cycle.
    change_only_on_en_or_rst_prev: assert property (
        @(posedge CLK) disable iff (RST) $changed(Q) |-> $past(RST || EN)
    );

    // Without reset in prior cycle, Q either holds or increments by 1.
    at_most_one_step_no_reset: assert property (
        @(posedge CLK) disable iff (RST) $past(!RST) |-> ((Q == $past(Q)) || (Q == $past(Q) + 4'd1))
    );

endmodule