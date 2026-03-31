```systemverilog
module top_module_sva (
    input logic clk,
    input logic areset,
    input logic load,
    input logic ena,
    input logic [3:0] data,
    output logic [3:0] q
);
    // Reset behavior: areset should drive q and shift_reg to 0
    reset: assert property (
        @(posedge clk) disable iff (!areset) (q == 4'b0) && (shift_reg == 4'b0)
    );

    // Load behavior: when load is high, q and shift_reg should be updated with data
    load_behavior: assert property (
        @(posedge clk) disable iff (!areset) (load |-> (q == data) && (shift_reg == data))
    );

    // Enable behavior: when ena is high, shift_reg should shift left by one bit
    enable_behavior: assert property (
        @(posedge clk) disable iff (!areset) (ena |-> (shift_reg == {1'b0, shift_reg[3:1]}))
    );

    // Shifted value behavior: shifted_value should always be {1'b0, shift_reg[3:1]}
    shifted_value_behavior: assert property (
        @(posedge clk) disable iff (!areset) (shifted_value == {1'b0, shift_reg[3:1]})
    );

    // Output behavior: when load and ena are high, q should be updated with data
    output_behavior: assert property (
        @(posedge clk) disable iff (!areset) (load && ena |-> (q == data))
    );

    // Output behavior: when load and ena are low, q should be updated with shifted_value
    output_behavior_low: assert property (
        @(posedge clk) disable iff (!areset) (!load && !ena |-> (q == shifted_value))
    );

    // Shift_reg behavior: shift_reg should be updated correctly based on load and ena
    shift_reg_behavior: assert property (
        @(posedge clk) disable iff (!areset) (load |-> (shift_reg == data)) else (ena |-> (shift_reg == {1'b0, shift_reg[3:1]}))
    );

    // Areset behavior: areset should drive q and shift_reg to 0
    areset_behavior: assert property (
        @(posedge clk) disable iff (!areset) (areset |-> (q == 4'b0) && (shift_reg == 4'b0))
    );

    // Load and enable behavior: when load and ena are high, q should be updated with data
    load_and_enable_behavior: assert property (
        @(posedge clk) disable iff (!areset) (load && ena |-> (q == data))
    );

    // Load and enable behavior: when load and ena are low, q should be updated with shifted_value
    load_and_enable_behavior_low: assert property (
        @(posedge clk) disable iff (!areset) (!load && !ena |-> (q == shifted_value))
    );
endmodule
```