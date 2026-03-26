module top_module_sva (
    input logic clk,
    input logic reset,
    input logic select,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [3:0] din,
    input logic load,
    input logic shift,
    input logic [7:0] out
);

    // Upper nibble always reflects the 4-bit sum of A and B.
    check_adder_output: assert property (
        @(posedge clk) disable iff (reset)
        out[7:4] == (A + B)
    );

    // A load captures din into the lower nibble on the next cycle.
    check_shift_load: assert property (
        @(posedge clk) disable iff (reset)
        load |=> out[3:0] == $past(din)
    );

    // A shift without load moves the lower nibble left and inserts 0.
    check_shift_left: assert property (
        @(posedge clk) disable iff (reset)
        (!load && shift) |=> out[3:0] == { $past(out[2:0]), 1'b0 }
    );

    // With neither load nor shift, the lower nibble holds its value.
    check_shift_hold: assert property (
        @(posedge clk) disable iff (reset)
        (!load && !shift) |=> out[3:0] == $past(out[3:0])
    );

    // Load takes priority over shift when both controls are asserted.
    check_load_priority: assert property (
        @(posedge clk) disable iff (reset)
        (load && shift) |=> out[3:0] == $past(din)
    );

endmodule