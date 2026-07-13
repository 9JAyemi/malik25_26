module dffre_sva #(
    parameter SIZE = 1
) (
    input logic [SIZE-1:0] din,
    input logic            rst,
    input logic            en,
    input logic            clk,
    input logic [SIZE-1:0] q,
    input logic            se,
    input logic [SIZE-1:0] si,
    input logic [SIZE-1:0] so
);

    // so is always driven by q.
    check_so_matches_q: assert property (
        @(posedge clk) disable iff (1'b0)
        so == q
    );

    // With se high, q captures si on the next cycle.
    check_scan_load: assert property (
        @(posedge clk) disable iff (1'b0)
        se |=> (q == $past(si))
    );

    // With se low and rst high, q is cleared to zero.
    check_reset_clears_q: assert property (
        @(posedge clk) disable iff (1'b0)
        (!se && rst) |=> (q == {SIZE{1'b0}})
    );

    // With se low, rst low, and en high, q captures din.
    check_enable_load: assert property (
        @(posedge clk) disable iff (1'b0)
        (!se && !rst && en) |=> (q == $past(din))
    );

    // With no active load condition, q holds its value.
    check_hold_when_idle: assert property (
        @(posedge clk) disable iff (1'b0)
        (!se && !rst && !en) |=> (q == $past(q))
    );

endmodule