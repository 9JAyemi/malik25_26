module binary_counter_sva (
    input logic CLK,
    input logic CLR_B,
    input logic LOAD,
    input logic [4:0] DATA_IN,
    output logic [4:0] Q
);
    parameter MAX_VALUE = 16;

    ///// Counter reset /////
    // At reset, the counter Q must be driven to 0.
    reset: assert property (
        @(posedge CLK) CLR_B |-> (Q == 0)
    );

    ///// Counter load /////
    // When LOAD is asserted, the counter Q must be loaded with DATA_IN.
    load: assert property (
        @(posedge CLK) LOAD |-> (Q == DATA_IN)
    );

    ///// Counter increment /////
    // When LOAD is not asserted and CLR_B is not asserted, the counter Q must increment.
    increment: assert property (
        @(posedge CLK) disable iff (CLR_B) !LOAD |-> (Q == Q + 1)
    );

    ///// Counter wraparound /////
    // When the counter reaches MAX_VALUE - 1, it must wrap around to 0.
    wraparound: assert property (
        @(posedge CLK) disable iff (CLR_B) Q == MAX_VALUE - 1 |-> (Q == 0)
    );

    ///// Counter stability /////
    // The counter Q must not change when CLR_B and LOAD are both not asserted.
    stability: assert property (
        @(posedge CLK) disable iff (CLR_B) !LOAD |-> Q == Q
    );

    ///// Counter range /////
    // The counter Q must always be within the range [0, MAX_VALUE - 1].
    range: assert property (
        @(posedge CLK) disable iff (CLR_B) (Q >= 0) && (Q <= MAX_VALUE - 1)
    );

    ///// Counter load and increment /////
    // When LOAD is asserted, the counter Q must not increment.
    load_and_increment: assert property (
        @(posedge CLK) LOAD |-> Q == DATA_IN
    );

    ///// Counter reset and load /////
    // When CLR_B is asserted, the counter Q must not load with DATA_IN.
    reset_and_load: assert property (
        @(posedge CLK) CLR_B |-> Q == 0
    );

    ///// Counter reset and increment /////
    // When CLR_B is asserted, the counter Q must not increment.
    reset_and_increment: assert property (
        @(posedge CLK) CLR_B |-> Q == 0
    );

    ///// Counter load and reset /////
    // When LOAD is asserted, the counter Q must not be reset.
    load_and_reset: assert property (
        @(posedge CLK) LOAD |-> Q == DATA_IN
    );

    ///// Counter increment and reset /////
    // When CLR_B is asserted, the counter Q must not increment.
    increment_and_reset: assert property (
        @(posedge CLK) CLR_B |-> Q == 0
    );
endmodule