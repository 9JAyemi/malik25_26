module counter_4bit_sva (
    input logic clk,
    input logic reset,
    input logic enable,
    input logic [3:0] count
);
    ///// Counter reset /////
    // At reset, the counter must be driven to 0.
    reset: assert property (
        @(posedge clk) disable iff (!reset) count == 4'b0000
    );

    ///// Counter enable /////
    // When enable is high, the counter should increment.
    enable: assert property (
        @(posedge clk) disable iff (!reset) (enable == 1'b1) |-> count == count + 1
    );

    ///// Counter behavior /////
    // The counter should not increment when enable is low.
    disable_enable: assert property (
        @(posedge clk) disable iff (!reset) (enable == 1'b0) |-> count == count
    );

    ///// Counter wrap-around /////
    // The counter should wrap around from 15 to 0.
    wrap_around: assert property (
        @(posedge clk) disable iff (!reset) (count == 4'b1111) |-> count == 4'b0000
    );

    ///// Counter stability /////
    // The counter should not change when reset is high.
    stability_reset: assert property (
        @(posedge clk) disable iff (reset) count == count
    );

    ///// Counter stability /////
    // The counter should not change when enable is high and reset is low.
    stability_enable: assert property (
        @(posedge clk) disable iff (!reset) (enable == 1'b1) |-> count == count
    );

    ///// Counter stability /////
    // The counter should not change when enable is low and reset is low.
    stability_no_change: assert property (
        @(posedge clk) disable iff (!reset) (enable == 1'b0) |-> count == count
    );

    ///// Counter behavior /////
    // The counter should increment by 1 on each positive edge of the clock when enable is high and reset is low.
    increment: assert property (
        @(posedge clk) disable iff (!reset) (enable == 1'b1) |-> count == count + 1
    );

    ///// Counter behavior /////
    // The counter should not increment when enable is low and reset is low.
    no_increment: assert property (
        @(posedge clk) disable iff (!reset) (enable == 1'b0) |-> count == count
    );
endmodule