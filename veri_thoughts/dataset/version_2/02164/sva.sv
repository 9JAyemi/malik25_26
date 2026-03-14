module dffr_sva #(
    parameter SIZE = 1
) (
    input logic                   clk,   // clock
    input logic                   rst,   // active-high synchronous reset
    input logic                   se,    // scan-enable
    input logic [SIZE-1:0]        din,   // data in
    input logic [SIZE-1:0]        si,    // scan in
    input logic [SIZE-1:0]        q,     // flop output
    input logic [SIZE-1:0]        so     // scan out (combinational mirror of q)
);
    // Clock: clk; Reset: rst (active-high synchronous).
    // Logic: Mixed — sequential flop for q; combinational so = q.
    // Behavior: se has priority; else if rst, q<=0; else q<=din.

    // so always mirrors q.
    check_so_mirrors_q: assert property (
        @(posedge clk) disable iff (rst) (so == q)
    );

    // On scan enable, q loads si on the next cycle (se has highest priority).
    check_scan_loads_si: assert property (
        @(posedge clk) disable iff (rst) $past(se) |-> (q == $past(si))
    );

    // With se deasserted, rst loads zero on the next cycle.
    check_sync_reset_loads_zero: assert property (
        @(posedge clk) disable iff (rst) $past((!se) && rst) |-> (q == {SIZE{1'b0}})
    );

    // With se deasserted and rst low, q loads din on the next cycle.
    check_functional_loads_din: assert property (
        @(posedge clk) disable iff (rst) $past((!se) && (!rst)) |-> (q == $past(din))
    );

    // In scan mode, so reflects previous si on the next cycle.
    check_so_follows_si_in_scan: assert property (
        @(posedge clk) disable iff (rst) $past(se) |-> (so == $past(si))
    );

    // After a reset cycle with se low, so is zero on the next cycle.
    check_so_zero_after_reset_cycle: assert property (
        @(posedge clk) disable iff (rst) $past((!se) && rst) |-> (so == {SIZE{1'b0}})
    );

    // If functional path selected and din equals prior q, q holds its value.
    check_hold_when_din_equals_q: assert property (
        @(posedge clk) disable iff (rst) $past((!se) && (!rst) && (din == q)) |-> (q == $past(q))
    );

    // If scan path selected and si equals prior q, q holds its value.
    check_hold_in_scan_when_si_equals_q: assert property (
        @(posedge clk) disable iff (rst) $past(se && (si == q)) |-> (q == $past(q))
    );

endmodule