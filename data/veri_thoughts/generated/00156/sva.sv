module pipereg_w32_sva (
    input logic clk,
    input logic resetn,
    input logic [31:0] d,
    input logic squashn,
    input logic en,
    input logic [31:0] q
);

    // Reset or squash clears q.
    check_clear_on_reset_or_squash: assert property (
        @(posedge clk) (!resetn || !squashn) |=> (q == 32'h00000000)
    );

    // Reset has priority over enable.
    check_reset_priority_over_enable: assert property (
        @(posedge clk) (!resetn && en) |=> (q == 32'h00000000)
    );

    // Squash has priority over enable.
    check_squash_priority_over_enable: assert property (
        @(posedge clk) disable iff (!resetn) (!squashn && en) |=> (q == 32'h00000000)
    );

    // Enable loads d when reset and squash are inactive.
    check_load_when_enabled: assert property (
        @(posedge clk) disable iff (!resetn) (squashn && en) |=> (q == $past(d))
    );

    // q holds its value when enable is low and no clear is active.
    check_hold_when_disabled: assert property (
        @(posedge clk) disable iff (!resetn) (squashn && !en) |=> $stable(q)
    );

endmodule