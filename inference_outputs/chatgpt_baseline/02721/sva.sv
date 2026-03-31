module dffre_sva #(
    parameter SIZE = 1
) (
    input  logic [SIZE-1:0] din, // data in
    input  logic            rst, // active-high synchronous reset
    input  logic            en,  // functional enable
    input  logic            clk, // clock
    input  logic [SIZE-1:0] q,   // output
    input  logic            se,  // scan-enable
    input  logic [SIZE-1:0] si,  // scan-input
    input  logic [SIZE-1:0] so   // scan-output
);

    // so continuously mirrors q.
    check_so_equals_q: assert property (
        @(posedge clk) so == q
    );

    // When scan-enable is high, q loads si on next cycle.
    check_scan_loads_si: assert property (
        @(posedge clk) disable iff (rst) (se == 1'b1) |=> (q == $past(si))
    );

    // When not in scan, reset high clears q to zero on next cycle.
    check_reset_clears_q: assert property (
        @(posedge clk) (se == 1'b0) && (rst == 1'b1) |=> (q == {SIZE{1'b0}})
    );

    // When not in scan and not in reset, en high loads din on next cycle.
    check_en_loads_din: assert property (
        @(posedge clk) disable iff (rst) (se == 1'b0) && (en == 1'b1) && (rst == 1'b0) |=> (q == $past(din))
    );

    // When not in scan and not in reset, en low holds q.
    check_hold_without_en: assert property (
        @(posedge clk) disable iff (rst) (se == 1'b0) && (rst == 1'b0) && (en == 1'b0) |=> (q == $past(q))
    );

    // When not in scan, reset high drives so to zero on next cycle (since so=q).
    check_reset_clears_so: assert property (
        @(posedge clk) (se == 1'b0) && (rst == 1'b1) |=> (so == {SIZE{1'b0}})
    );

endmodule