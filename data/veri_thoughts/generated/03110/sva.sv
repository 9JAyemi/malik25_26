module counter_sva (
    input logic       clk,
    input logic       rst,
    input logic       en,
    input logic [3:0] count
);

    // Reset forces the count to zero.
    check_reset_clears_count: assert property (
        @(posedge clk) (!rst) |-> (count == 4'b0000)
    );

    // With enable low, the count holds its value.
    check_hold_when_disabled: assert property (
        @(posedge clk) disable iff (!rst)
        (!en) |=> (count == $past(count))
    );

    // With enable high, the count increments by one.
    check_increment_when_enabled: assert property (
        @(posedge clk) disable iff (!rst)
        en |=> (count == ($past(count) + 4'd1))
    );

    // The 4-bit counter wraps from 15 back to 0 when enabled.
    check_wrap_on_max: assert property (
        @(posedge clk) disable iff (!rst)
        (en && (count == 4'hf)) |=> (count == 4'h0)
    );

    // Any count change must be caused by a previously enabled cycle.
    check_change_requires_enable: assert property (
        @(posedge clk) disable iff (!rst)
        ($past(rst) && (count != $past(count))) |-> $past(en)
    );

endmodule