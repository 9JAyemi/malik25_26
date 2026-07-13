module pipereg_w26_sva (
    input logic clk,
    input logic resetn,
    input logic en,
    input logic squashn,
    input logic [25:0] d,
    input logic [25:0] q
);
    // Reset or squash forces q to zero on the next cycle.
    reset_or_squash_clears_q: assert property (
        @(posedge clk) disable iff (!resetn) (resetn == 1'b0 || squashn == 1'b0) |=> (q == 26'b0)
    );

    // When enabled and not in reset/squash, q captures d on the next cycle.
    capture_when_enabled: assert property (
        @(posedge clk) disable iff (!resetn) (en == 1'b1 && squashn == 1'b1) |=> (q == $past(d))
    );

    // When disabled and not in reset/squash, q holds its value.
    hold_when_disabled: assert property (
        @(posedge clk) disable iff (!resetn) (en == 1'b0 && squashn == 1'b1) |=> (q == $past(q))
    );

    // Any change in q must be caused by reset/squash or an enabled cycle.
    change_requires_enable_or_reset: assert property (
        @(posedge clk) disable iff (!resetn) (q != $past(q)) |-> ($past(resetn == 1'b0 || squashn == 1'b0 || en == 1'b1))
    );

    // If reset/squash is high and d differs from q, q must change next cycle.
    change_when_enabled_and_d_differs: assert property (
        @(posedge clk) disable iff (!resetn) (resetn == 1'b1 && squashn == 1'b1 && d != q) |=> (q != $past(q))
    );

    // If reset/squash is high and d equals q, q must not change next cycle.
    no_change_when_enabled_and_d_equals_q: assert property (
        @(posedge clk) disable iff (!resetn) (resetn == 1'b1 && squashn == 1'b1 && d == q) |=> (q == $past(q))
    );

    // If reset/squash is high and en is low, q must not change next cycle.
    no_change_when_disabled_and_reset_clears: assert property (
        @(posedge clk) disable iff (!resetn) (resetn == 1'b1 && squashn == 1'b1 && en == 1'b0) |=> (q == $past(q))
    );

    // If reset/squash is high and en is high, q must change next cycle.
    change_when_enabled_and_reset_clears: assert property (
        @(posedge clk) disable iff (!resetn) (resetn == 1'b1 && squashn == 1'b1 && en == 1'b1) |=> (q != $past(q))
    );

    // If reset/squash is high and d differs from q, q must change next cycle.
    change_when_enabled_and_d_differs: assert property (
        @(posedge clk) disable iff (!resetn) (resetn == 1'b1 && squashn == 1'b1 && d != q) |=> (q != $past(q))
    );

    // If reset/squash is high and d equals q, q must not change next cycle.
    no_change_when_enabled_and_d_equals_q: assert property (
        @(posedge clk) disable iff (!resetn) (resetn == 1'b1 && squashn == 1'b1 && d == q) |=> (q == $past(q))
    );
endmodule