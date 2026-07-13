module components_dff_en_rst_sva (
    input logic clk,
    input logic rst,
    input logic en,
    input logic [31:0] d,
    input logic [31:0] q
);

// Reset drives q to 0 on the next clock.
    check_reset_clears_q: assert property (
        @(posedge clk) rst |=> (q == 32'd0)
    );

// With reset low and en high, q captures d on the next clock.
    check_capture_when_en_high: assert property (
        @(posedge clk) disable iff (rst) en |=> (q == $past(d))
    );

// With reset low and en low, q holds its previous value.
    check_hold_when_en_low: assert property (
        @(posedge clk) disable iff (rst) !en |=> (q == $past(q))
    );

endmodule
