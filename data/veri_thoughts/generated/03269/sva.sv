module Register_sva (
    input logic        clk,
    input logic        reset,
    input logic        en,
    input logic        byte_lo,
    input logic        byte_hi,
    input logic [15:0] d,
    input logic [15:0] q
);

    // Synchronous reset clears the full register.
    check_reset_clears_q: assert property (
        @(posedge clk)
        reset |=> (q == 16'h0000)
    );

    // Low byte updates from d when enabled and selected.
    check_low_byte_write: assert property (
        @(posedge clk) disable iff (reset)
        (en && byte_lo) |=> (q[7:0] == $past(d[7:0]))
    );

    // Low byte holds its value when not written.
    check_low_byte_hold: assert property (
        @(posedge clk) disable iff (reset)
        (!en || !byte_lo) |=> (q[7:0] == $past(q[7:0]))
    );

    // High byte updates from d when enabled and selected.
    check_high_byte_write: assert property (
        @(posedge clk) disable iff (reset)
        (en && byte_hi) |=> (q[15:8] == $past(d[15:8]))
    );

    // High byte holds its value when not written.
    check_high_byte_hold: assert property (
        @(posedge clk) disable iff (reset)
        (!en || !byte_hi) |=> (q[15:8] == $past(q[15:8]))
    );

endmodule