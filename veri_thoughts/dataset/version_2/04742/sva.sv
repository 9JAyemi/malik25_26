module dffe_sva #(
    parameter SIZE = 8
)(
    input logic [SIZE-1:0] din,
    input logic en,
    input logic clk,
    input logic [SIZE-1:0] q,
    input logic se,
    input logic [SIZE-1:0] si,
    input logic [SIZE-1:0] so
);

    // so mirrors q.
    check_so_matches_q: assert property (
        @(posedge clk) (so == q)
    );

    // Scan enable loads si into q on the next cycle.
    check_scan_load: assert property (
        @(posedge clk) se |=> (q == $past(si))
    );

    // Data enable loads din into q when scan is disabled.
    check_data_load: assert property (
        @(posedge clk) (!se && en) |=> (q == $past(din))
    );

    // q holds its value when neither scan nor data load is selected.
    check_hold_without_enable: assert property (
        @(posedge clk) (!se && !en) |=> (q == $past(q))
    );

    // Scan path has priority when se and en are both high.
    check_scan_priority_over_data: assert property (
        @(posedge clk) (se && en) |=> (q == $past(si))
    );

endmodule