module dffrl_s_sva #(
    parameter SIZE = 1
) (
    input  logic                  clk,
    input  logic                  rst_l,
    input  logic                  se,
    input  logic [SIZE-1:0]       din,
    input  logic [SIZE-1:0]       si,
    input  logic [SIZE-1:0]       q,
    input  logic [SIZE-1:0]       so
);
    ///// Reset behavior /////
    // When reset is asserted (active-low), q is driven to 0 on the clock edge.
    check_reset_clears_q: assert property (
        @(posedge clk) !rst_l |-> (q == {SIZE{1'b0}})
    );

    ///// Functional capture behavior (common to both builds) /////
    // When not in reset and se was 0 last cycle, q captures din.
    check_capture_din_when_se0: assert property (
        @(posedge clk) disable iff (!rst_l) ($past(rst_l) && ($past(se) == 1'b0)) |-> (q == $past(din))
    );

    // When not in reset, se was 0, and din equaled q last cycle, q holds its value.
    check_hold_when_se0_and_din_matches_q: assert property (
        @(posedge clk) disable iff (!rst_l) ($past(rst_l) && ($past(se) == 1'b0) && ($past(din) == $past(q))) |-> (q == $past(q))
    );

`ifdef NO_SCAN
    ///// NO_SCAN build /////
    // When not in reset, q always captures din.
    check_noscan_captures_din: assert property (
        @(posedge clk) disable iff (!rst_l) $past(rst_l) |-> (q == $past(din))
    );
`else
    ///// Scan-enabled build /////
    // Combined next-state function: q captures si when se=1, else din, when not in reset.
    check_scan_combined_nextstate: assert property (
        @(posedge clk) disable iff (!rst_l) $past(rst_l) |-> (q == ($past(se) ? $past(si) : $past(din)))
    );

    // When not in reset and se was 1 last cycle, q captures si.
    check_capture_si_when_se1: assert property (
        @(posedge clk) disable iff (!rst_l) ($past(rst_l) && ($past(se) == 1'b1)) |-> (q == $past(si))
    );

    // so directly reflects q at all times (when property enabled).
    check_so_equals_q: assert property (
        @(posedge clk) disable iff (!rst_l) (so == q)
    );

    // When reset is asserted (active-low), so is driven to 0 via so=q.
    check_reset_clears_so: assert property (
        @(posedge clk) !rst_l |-> (so == {SIZE{1'b0}})
    );

    // When not in reset and se was 0, so reflects previous din (via so=q).
    check_so_follows_prev_din_when_se0: assert property (
        @(posedge clk) disable iff (!rst_l) ($past(rst_l) && ($past(se) == 1'b0)) |-> (so == $past(din))
    );

    // When not in reset and se was 1, so reflects previous si (via so=q).
    check_so_follows_prev_si_when_se1: assert property (
        @(posedge clk) disable iff (!rst_l) ($past(rst_l) && ($past(se) == 1'b1)) |-> (so == $past(si))
    );
`endif

endmodule