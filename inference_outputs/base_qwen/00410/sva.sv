```systemverilog
module up_down_counter_sva (
    input logic clk,
    input logic load,
    input logic up_down,
    output logic [2:0] out
);
    ///// Load behavior /////
    // When load is asserted, the counter should reset to 0.
    load_reset: assert property (
        @(posedge clk) disable iff (!clk) load |-> (out == 3'b000)
    );

    ///// Up/Down behavior /////
    // When up_down is asserted, the counter should increment.
    up_count: assert property (
        @(posedge clk) disable iff (!clk) up_down |-> (out == out + 1)
    );

    // When up_down is deasserted, the counter should decrement.
    down_count: assert property (
        @(posedge clk) disable iff (!clk) !up_down |-> (out == out - 1)
    );

    ///// Sequential logic check /////
    // The counter should only change on the positive edge of the clock.
    sequential_logic: assert property (
        @(posedge clk) disable iff (!clk) (out == out @ (posedge clk))
    );

    ///// Combinational logic check /////
    // The counter should not change on the negative edge of the clock.
    combinational_logic: assert property (
        @(negedge clk) disable iff (!clk) (out == out @ (posedge clk))
    );

    ///// Load and up_down cannot be asserted simultaneously /////
    // Simultaneous load and up_down should not occur.
    simultaneous_load_up_down: assert property (
        @(posedge clk) disable iff (!clk) !(load && up_down)
    );

    ///// Counter value should be within valid range [0, 7] /////
    // The counter should not exceed the valid range.
    counter_range: assert property (
        @(posedge clk) disable iff (!clk) (out >= 3'b000 && out <= 3'b111)
    );

    ///// Load should not be asserted when counter is at maximum value /////
    // Load should not be asserted when the counter is at its maximum value.
    load_at_max: assert property (
        @(posedge clk) disable iff (!clk) !(load && (out == 3'b111))
    );

    ///// Load should not be asserted when counter is at minimum value /////
    // Load should not be asserted when the counter is at its minimum value.
    load_at_min: assert property (
        @(posedge clk) disable iff (!clk) !(load && (out == 3'b000))
    );

    ///// Up/Down should not be asserted when counter is at maximum value /////
    // Up/Down should not be asserted when the counter is at its maximum value.
    up_at_max: assert property (
        @(posedge clk) disable iff (!clk) !(up_down && (out == 3'b111))
    );

    ///// Up/Down should not be asserted when counter is at minimum value /////
    // Up/Down should not be asserted when the counter is at its minimum value.
    down_at_min: assert property (
        @(posedge clk) disable iff (!clk) !(up_down && (out == 3'b000))
    );
endmodule
```