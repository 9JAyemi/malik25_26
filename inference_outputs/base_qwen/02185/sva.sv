module counter_sva (
    input logic CLK,
    input logic reset,
    input logic enable,
    output logic [3:0] count
);
    ///// Counter reset /////
    // At reset assertion, the counter must be driven to 0.
    reset: assert property (
        @(posedge CLK) reset |-> (count == 4'b0)
    );

    ///// Counter enable /////
    // When enable is high, the counter should increment on each clock edge.
    enable: assert property (
        @(posedge CLK) disable iff (reset) enable |-> count == count + 1
    );

    ///// Counter disable /////
    // When enable is low, the counter should not increment.
    disable: assert property (
        @(posedge CLK) disable iff (reset) !enable |-> count == count
    );
endmodule