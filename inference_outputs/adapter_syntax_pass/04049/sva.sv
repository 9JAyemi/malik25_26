module pipereg_w26_sva (
    input logic clk,
    input logic resetn,
    input logic en,
    input logic squashn,
    input logic [25:0] d,
    input logic [25:0] q
);

    // Reset or squash forces q to zero on the next cycle.
    check_reset_or_squash_clears_q: assert property (
        @(posedge clk) disable iff ($initstate)
        (!resetn || !squashn) |=> (q == 26'h00000000)
    );

    // With enable high, q captures d on the next cycle.
    check_capture_when_enabled: assert property (
        @(posedge clk) disable iff (!resetn || !squashn || $initstate)
        (en && squashn) |=> (q == $past(d))
    );

    // With enable low, q holds its previous value.
    check_hold_when_disabled: assert property (
        @(posedge clk) disable iff (!resetn || !squashn || $initstate)
        (!en && squashn) |=> (q == $past(q))
    );

endmodule