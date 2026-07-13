module binary_counter_sva (
    input logic       CLK,
    input logic       RST,
    input logic       EN,
    input logic [3:0] q
);

    // Reset drives q to zero by the following clock edge.
    check_reset_clears_q: assert property (
        @(posedge CLK) RST |=> (q == 4'b0000)
    );

    // When enabled, q increments by one on the next clock.
    check_increment_when_enabled: assert property (
        @(posedge CLK) disable iff (RST)
        EN |=> (q == ($past(q) + 4'd1))
    );

    // When disabled, q holds its value on the next clock.
    check_hold_when_disabled: assert property (
        @(posedge CLK) disable iff (RST)
        !EN |=> (q == $past(q))
    );

    // A terminal count increment wraps q from 4'hF to 4'h0.
    check_wrap_from_max_count: assert property (
        @(posedge CLK) disable iff (RST)
        EN && (q == 4'hF) |=> (q == 4'h0)
    );

endmodule