module counter_4bit_async_sva (
    input logic clk,
    input logic rst,
    input logic en,
    input logic [3:0] out
);

    // Active-low reset clears the counter output.
    check_reset_clears_out: assert property (
        @(posedge clk) !rst |-> (out == 4'b0000)
    );

    // Enabled cycles increment the counter by one.
    check_increment_when_enabled: assert property (
        @(posedge clk) disable iff (!rst)
        en |=> (out == ($past(out) + 4'd1))
    );

    // Disabled cycles hold the counter value.
    check_hold_when_disabled: assert property (
        @(posedge clk) disable iff (!rst)
        !en |=> (out == $past(out))
    );

    // The next state follows the prior cycle's enable.
    check_next_state_follows_enable: assert property (
        @(posedge clk) disable iff (!rst)
        1'b1 |=> (out == ($past(en) ? ($past(out) + 4'd1) : $past(out)))
    );

    // The 4-bit counter wraps from 15 back to 0.
    check_wrap_on_overflow: assert property (
        @(posedge clk) disable iff (!rst)
        (en && (out == 4'hF)) |=> (out == 4'h0)
    );

endmodule