module sync_counter_sva (
    input logic       CLK,
    input logic       RST,
    input logic       EN,
    input logic [3:0] Q
);

    // RST is the active-high synchronous reset.
    // EN controls a 4-bit sequential up-counter on CLK.

    // Reset loads the counter with zero.
    check_reset_clears_q: assert property (
        @(posedge CLK) RST |=> (Q == 4'b0000)
    );

    // When enabled, the counter increments by one.
    check_enable_increments_q: assert property (
        @(posedge CLK) disable iff (RST)
        EN |=> (Q == ($past(Q) + 4'd1))
    );

    // When not enabled, the counter holds its value.
    check_disable_holds_q: assert property (
        @(posedge CLK) disable iff (RST)
        !EN |=> (Q == $past(Q))
    );

    // Counting from 4'hF wraps the 4-bit counter to zero.
    check_counter_wraps: assert property (
        @(posedge CLK) disable iff (RST)
        (EN && (Q == 4'hF)) |=> (Q == 4'h0)
    );

endmodule