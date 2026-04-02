module CounterAssertions (
    input logic Clock,
    input logic Reset,
    input logic Set,
    input logic Load,
    input logic Enable,
    input logic [Width-1:0] In,
    output logic [Width-1:0] Count
);

parameter Width = 32;

    ///// Counter reset /////
    // At reset, the counter must be initialized to the initial value.
    reset: assert property (
        @(posedge Clock) !Reset |-> (Count == Initial)
    );

    ///// Counter enable /////
    // The counter can only be incremented or decremented when Enable is high.
    enable: assert property (
        @(posedge Clock) disable iff (!Reset) (Enable == 1'b0) |-> (Count == $past(Count))
    );

    ///// Counter load /////
    // The counter can only be loaded when Load is high.
    load: assert property (
        @(posedge Clock) disable iff (!Reset) (Load == 1'b0) |-> (Count == $past(Count))
    );

    ///// Counter increment /////
    // The counter should increment when Enable is high and Load is low.
    increment: assert property (
        @(posedge Clock) disable iff (!Reset) (Enable == 1'b1) && (Load == 1'b0) |-> (Count == $past(Count) + 1)
    );

    ///// Counter decrement /////
    // The counter should decrement when Enable is high, Load is low, and Down is high.
    decrement: assert property (
        @(posedge Clock) disable iff (!Reset) (Enable == 1'b1) && (Load == 1'b0) && (Down == 1'b1) |-> (Count == $past(Count) - 1)
    );

    ///// Counter no limit /////
    // The counter should not exceed the maximum value when Limited is low.
    no_limit: assert property (
        @(posedge Clock) disable iff (!Reset) (Limited == 1'b0) |-> (Count <= {Width{1'b1}})
    );

    ///// Counter set /////
    // The counter should be set to the initial value when Set is high.
    set: assert property (
        @(posedge Clock) disable iff (!Reset) (Set == 1'b1) |-> (Count == Initial)
    );

    ///// Counter input /////
    // The counter should be loaded with the input value when Load is high.
    input_load: assert property (
        @(posedge Clock) disable iff (!Reset) (Load == 1'b1) |-> (Count == In)
    );

endmodule