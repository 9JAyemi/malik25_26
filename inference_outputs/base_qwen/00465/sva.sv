module up_counter_2bit_sva (
    input logic clk,
    input logic reset,
    input logic enable,
    output logic [1:0] count
);
    ///// Counter reset /////
    // At reset, the counter must be driven to 0.
    reset: assert property (
        @(posedge clk) reset |-> (count == 2'b00)
    );

    ///// Counter enable /////
    // The counter can only increment when enable is high.
    enable_check: assert property (
        @(posedge clk) disable iff (reset) (enable |-> count == count + 1)
    );

    ///// Counter overflow /////
    // The counter must not overflow (i.e., it should not exceed 2'b11).
    overflow_check: assert property (
        @(posedge clk) disable iff (reset) (count != 2'b11)
    );

    ///// Counter stability /////
    // The counter should not change when enable is low.
    stability_check: assert property (
        @(posedge clk) disable iff (reset) (!enable |-> count == count)
    );
endmodule