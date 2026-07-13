module pipereg_w26_sva (
    input logic clk,
    input logic resetn,
    input logic en,
    input logic squashn,
    input logic [25:0] d,
    input logic [25:0] q
);

// Reset low forces q to zero on the next clock.
    check_reset_clears_q: assert property (
        @(posedge clk) !resetn |=> (q == 26'h0)
    );

// Squash low forces q to zero on the next clock.
    check_squash_clears_q: assert property (
        @(posedge clk) !squashn |=> (q == 26'h0)
    );

// When enabled and not in reset/squash, q captures d on the next clock.
    check_capture_when_enabled: assert property (
        @(posedge clk) disable iff (!resetn || !squashn) en |=> (q == $past(d))
    );

// When not enabled and not in reset/squash, q holds its previous value.
    check_hold_when_disabled: assert property (
        @(posedge clk) disable iff (!resetn || !squashn) !en |=> (q == $past(q))
    );

endmodule
