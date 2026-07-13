module dffre_sva (
    input logic [0:0] din,
    input logic       rst,
    input logic       en,
    input logic       clk,
    input logic [0:0] q,
    input logic       se,
    input logic [0:0] si,
    input logic [0:0] so
);

// Scan mode loads q from si on the next cycle.
    check_scan_loads_q: assert property (
        @(posedge clk) se |=> (q == $past(si))
    );

// Scan mode has priority over reset when both are asserted.
    check_scan_priority_over_reset: assert property (
        @(posedge clk) (se && rst) |=> (q == $past(si))
    );

// Scan mode has priority over enable when both are asserted.
    check_scan_priority_over_enable: assert property (
        @(posedge clk) (se && en) |=> (q == $past(si))
    );

// Reset drives q low when scan and enable are both low.
    check_reset_clears_q: assert property (
        @(posedge clk) (!se && rst) |=> (q == 1'b0)
    );

// Enable loads q from din when scan and reset are both low.
    check_enable_loads_q: assert property (
        @(posedge clk) (!se && !rst && en) |=> (q == $past(din))
    );

// With no control active, q holds its previous value.
    check_hold_when_idle: assert property (
        @(posedge clk) (!se && !rst && !en) |=> (q == $past(q))
    );

// so is a direct copy of q.
    check_so_follows_q: assert property (
        @(posedge clk) (so == q)
    );

endmodule
