module binary_counter_sva(
    input logic       clk,
    input logic       rst,
    input logic       en,
    input logic [3:0] out
);

    // Reset clears the counter on the next sampled cycle.
    check_reset_clears_out: assert property (
        @(posedge clk) rst |=> (out == 4'b0000)
    );

    // Reset takes priority over enable and still clears the counter.
    check_reset_priority_over_enable: assert property (
        @(posedge clk) (rst && en) |=> (out == 4'b0000)
    );

    // When enabled outside reset, the counter increments by one.
    check_increment_when_enabled: assert property (
        @(posedge clk) disable iff (rst)
        en |=> (out == ($past(out) + 4'd1))
    );

    // When disabled outside reset, the counter holds its value.
    check_hold_when_disabled: assert property (
        @(posedge clk) disable iff (rst)
        !en |=> (out == $past(out))
    );

    // Outside reset, the next state is either hold or increment.
    check_only_hold_or_increment: assert property (
        @(posedge clk) disable iff (rst)
        1'b1 |=> ((out == $past(out)) || (out == ($past(out) + 4'd1)))
    );

    // Enabling the counter at 4'hF wraps it back to 4'h0.
    check_wrap_from_max: assert property (
        @(posedge clk) disable iff (rst)
        (en && (out == 4'hF)) |=> (out == 4'h0)
    );

endmodule