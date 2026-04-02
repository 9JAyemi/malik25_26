module counter_sva(
    input logic clk,
    input logic rst,
    input logic en,
    input logic [1:0] count
);
    // Reset behavior: count should be 00 at reset
    reset: assert property (
        @(posedge clk) disable iff (!rst) count == 2'b00
    );

    // Enable behavior: count should increment when enabled and not at reset
    enable: assert property (
        @(posedge clk) disable iff (!rst) (en == 1) |-> count != 2'b11
    );

    // Count increment behavior: count should increment by 1 when enabled and not at reset
    increment: assert property (
        @(posedge clk) disable iff (!rst) (en == 1) |-> count == 2'b11
    );

    // Count wrap-around behavior: count should wrap around from 11 to 00 when enabled
    wrap_around: assert property (
        @(posedge clk) disable iff (!rst) (en == 1 && count == 2'b11) |-> count == 2'b00
    );

    // Count should not change when disabled and not at reset
    disabled: assert property (
        @(posedge clk) disable iff (!rst) (en == 0) |-> count == count
    );

    // Count should not change at reset
    reset_count: assert property (
        @(posedge clk) !rst |-> count == count
    );
endmodule