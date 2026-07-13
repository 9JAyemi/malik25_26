module counter_4bit_sva (
    input logic       clk,
    input logic       rst,
    input logic       en,
    input logic [3:0] out
);

    // A sampled low reset clears the counter by the next clock.
    check_reset_clears_counter: assert property (
        @(posedge clk) (!rst) |=> (out == 4'b0000)
    );

    // With enable low, the counter holds its previous value.
    check_hold_when_disabled: assert property (
        @(posedge clk) disable iff (!rst) (!en) |=> (out == $past(out))
    );

    // With enable high below 4'hF, the counter increments by one.
    check_increment_when_enabled: assert property (
        @(posedge clk) disable iff (!rst) (en && (out != 4'hF)) |=> (out == ($past(out) + 4'd1))
    );

    // With enable high at 4'hF, the counter wraps to zero.
    check_wrap_when_enabled_at_max: assert property (
        @(posedge clk) disable iff (!rst) (en && (out == 4'hF)) |=> (out == 4'h0)
    );

    // An enabled cycle always changes the counter value.
    check_change_when_enabled: assert property (
        @(posedge clk) disable iff (!rst) en |=> (out != $past(out))
    );

endmodule