```systemverilog
module shift_register_4bit_sva (
    input CLK,
    input LOAD,
    input CLR,
    input [3:0] D,
    output reg [3:0] Q,
    output reg [3:0] Q_next
);
    ///// Shift register behavior /////
    // Q should shift left by one bit on each clock cycle when LOAD is LOW and CLR is LOW.
    shift_left: assert property (
        @(posedge CLK) disable iff (!CLR) (LOAD == 1'b0) |-> (Q == {Q[2:0], D[3]})
    );
    // Q_next should match Q on each clock cycle.
    next_match: assert property (
        @(posedge CLK) disable iff (!CLR) Q_next == Q
    );
    // Q should be reset to 0 when CLR is HIGH.
    reset_to_zero: assert property (
        @(posedge CLK) CLR |-> Q == 4'b0000
    );
    // Q_next should be reset to 0 when CLR is HIGH.
    next_reset_to_zero: assert property (
        @(posedge CLK) CLR |-> Q_next == 4'b0000
    );
    // Q should not change when CLR is HIGH.
    no_change_on_reset: assert property (
        @(posedge CLK) CLR |-> Q == Q
    );
    // Q_next should not change when CLR is HIGH.
    next_no_change_on_reset: assert property (
        @(posedge CLK) CLR |-> Q_next == Q_next
    );
    // Q should match D when LOAD is HIGH and CLR is LOW.
    load_match: assert property (
        @(posedge CLK) disable iff (!CLR) (LOAD == 1'b1) |-> Q == D
    );
    // Q_next should match D when LOAD is HIGH and CLR is LOW.
    next_load_match: assert property (
        @(posedge CLK) disable iff (!CLR) (LOAD == 1'b1) |-> Q_next == D
    );
    // Q should not change when LOAD is LOW and CLR is LOW.
    no_change_on_load: assert property (
        @(posedge CLK) disable iff (!CLR) (LOAD == 1'b0) |-> Q == Q
    );
    // Q_next should not change when LOAD is LOW and CLR is LOW.
    next_no_change_on_load: assert property (
        @(posedge CLK) disable iff (!CLR) (LOAD == 1'b0) |-> Q_next == Q_next
    );
endmodule
```