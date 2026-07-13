module reg_4bit_async_reset_enable_sva (
    input logic clk,
    input logic rst,
    input logic en,
    input logic [3:0] din,
    input logic [3:0] dout
);

    // Active-low reset forces dout to zero on any sampled clock.
    check_reset_clears_dout: assert property (
        @(posedge clk) (!rst) |-> (dout == 4'b0000)
    );

    // A sampled reset low leaves dout at zero on the following sampled clock.
    check_post_reset_stays_zero: assert property (
        @(posedge clk) (!rst) |=> (dout == 4'b0000)
    );

    // With enable low, dout either holds its value or has been asynchronously cleared to zero.
    check_disabled_cycle_holds_or_resets: assert property (
        @(posedge clk) disable iff (!rst)
        (!en) |=> ((dout == 4'b0000) || (dout == $past(dout)))
    );

    // With enable high, dout either captures the prior din or has been asynchronously cleared to zero.
    check_enabled_cycle_loads_or_resets: assert property (
        @(posedge clk) disable iff (!rst)
        en |=> ((dout == 4'b0000) || (dout == $past(din)))
    );

endmodule