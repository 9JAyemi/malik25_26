module pipereg_w26_sva(
    input logic clk,
    input logic resetn,
    input logic [25:0] d,
    input logic squashn,
    input logic en,
    input logic [25:0] q
);

    // Low reset clears q on the next cycle.
    check_reset_clears_q: assert property (
        @(posedge clk) !resetn |=> (q == 26'b0)
    );

    // Low squash clears q on the next cycle.
    check_squash_clears_q: assert property (
        @(posedge clk) disable iff (!resetn) (!squashn) |=> (q == 26'b0)
    );

    // Enable captures d into q on the next cycle.
    check_enable_captures_d: assert property (
        @(posedge clk) disable iff (!resetn) (squashn && en) |=> (q == $past(d))
    );

    // Without enable or clear, q holds its value.
    check_hold_when_disabled: assert property (
        @(posedge clk) disable iff (!resetn) (squashn && !en) |=> (q == $past(q))
    );

    // Squash takes priority over enable.
    check_squash_overrides_enable: assert property (
        @(posedge clk) disable iff (!resetn) (!squashn && en) |=> (q == 26'b0)
    );

endmodule