module top_module_sva (
    input logic clk,
    input logic slowena,
    input logic reset,
    input logic [1:0] a,
    input logic [1:0] b,
    input logic [7:0] q
);

    // A low reset clears q by the next clock sample.
    check_reset_clears_q: assert property (
        @(posedge clk) !reset |=> (q == 8'h00)
    );

    // q is always a zero-extended 4-bit value.
    check_q_upper_nibble_zero: assert property (
        @(posedge clk) disable iff (!reset) (q[7:4] == 4'h0)
    );

    // When paused, q holds its value regardless of a or b.
    check_q_holds_when_paused: assert property (
        @(posedge clk) disable iff (!reset) (!slowena) |=> (q == $past(q))
    );

    // When enabled, q increments by one modulo 16.
    check_q_increments_when_enabled: assert property (
        @(posedge clk) disable iff (!reset) slowena |=> (q[3:0] == ($past(q[3:0]) + 4'd1))
    );

    // Releasing reset while paused keeps q at zero on the next cycle.
    check_reset_release_paused_keeps_zero: assert property (
        @(posedge clk) disable iff (!reset) ($rose(reset) && !slowena) |=> (q == 8'h00)
    );

    // Releasing reset while enabled starts counting from one on the next cycle.
    check_reset_release_enabled_starts_one: assert property (
        @(posedge clk) disable iff (!reset) ($rose(reset) && slowena) |=> (q == 8'h01)
    );

endmodule