```systemverilog
module top_module_sva (
    input logic clk,
    input logic rst_n,
    input logic [15:0] A,
    input logic [15:0] B,
    input logic [3:0] shift_amount,
    output logic [15:0] result
);

    // Ensure magnitude comparator correctly sets A_greater_B
    magnitude_comparator_sva: assert property (
        @(posedge clk) disable iff (!rst_n) (A > B) |-> (A_greater_B == 1'b1)
    ) else $error("Magnitude comparator did not set A_greater_B correctly");

    magnitude_comparator_sva2: assert property (
        @(posedge clk) disable iff (!rst_n) (A <= B) |-> (A_greater_B == 1'b0)
    ) else $error("Magnitude comparator did not set A_greater_B correctly");

    // Ensure barrel shifter correctly shifts based on A_greater_B
    barrel_shifter_sva: assert property (
        @(posedge clk) disable iff (!rst_n) (A_greater_B && (A > B)) |-> (result == A << shift_amount)
    ) else $error("Barrel shifter did not shift A correctly");

    barrel_shifter_sva2: assert property (
        @(posedge clk) disable iff (!rst_n) (!A_greater_B && (A < B)) |-> (result == B >> shift_amount)
    ) else $error("Barrel shifter did not shift B correctly");

    barrel_shifter_sva3: assert property (
        @(posedge clk) disable iff (!rst_n) (A_greater_B == A < B) |-> (result == A)
    ) else $error("Barrel shifter did not handle equal values correctly");

    // Ensure result is zero at reset
    reset_result_sva: assert property (
        @(posedge clk) !rst_n |-> (result == 16'b0)
    ) else $error("Result did not reset to zero");

endmodule
```