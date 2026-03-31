module dffre_sva #(
    parameter SIZE = 1
) (
    input  logic                 clk,
    input  logic                 rst,
    input  logic                 en,
    input  logic                 se,
    input  logic [SIZE-1:0]      din,
    input  logic [SIZE-1:0]      si,
    input  logic [SIZE-1:0]      q,
    input  logic [SIZE-1:0]      so
);

    // so is a direct reflection of q.
    check_so_matches_q: assert property (
        @(posedge clk) disable iff (rst)
        so == q
    );

    // Scan mode loads si into q.
    check_scan_loads_si: assert property (
        @(posedge clk) disable iff (rst)
        se |=> (q == $past(si))
    );

    // Scan mode drives so from the loaded si.
    check_scan_loads_so: assert property (
        @(posedge clk) disable iff (rst)
        se |=> (so == $past(si))
    );

    // Reset clears q when scan mode is inactive.
    check_reset_clears_q: assert property (
        @(posedge clk) disable iff (rst)
        (!se && rst) |=> (q == {SIZE{1'b0}})
    );

    // Reset clears so when scan mode is inactive.
    check_reset_clears_so: assert property (
        @(posedge clk) disable iff (rst)
        (!se && rst) |=> (so == {SIZE{1'b0}})
    );

    // With scan and reset inactive, enable loads din into q.
    check_enable_loads_din: assert property (
        @(posedge clk) disable iff (rst)
        (!se && !rst && en) |=> (q == $past(din))
    );

    // With scan and reset inactive, enable drives din onto so.
    check_enable_loads_so: assert property (
        @(posedge clk) disable iff (rst)
        (!se && !rst && en) |=> (so == $past(din))
    );

    // With scan and reset inactive, enable has no effect on q.
    check_enable_no_effect_when_disabled: assert property (
        @(posedge clk) disable iff (rst)
        (!se && !rst && !en) |=> (q == $past(q))
    );

    // With scan and reset inactive, enable has no effect on so.
    check_enable_no_effect_on_so: assert property (
        @(posedge clk) disable iff (rst)
        (!se && !rst && !en) |=> (so == $past(so))
    );

    // With scan and reset inactive, q holds its value when enable is low.
    check_hold_when_disabled: assert property (
        @(posedge clk) disable iff (rst)
        (!se && !rst && !en) |=> (q == $past(q))
    );

    // With scan and reset inactive, so holds its value when enable is low.
    check_hold_so_when_disabled: assert property (
        @(posedge clk) disable iff (rst)
        (!se && !rst && !en) |=> (so == $past(so))
    );

endmodule