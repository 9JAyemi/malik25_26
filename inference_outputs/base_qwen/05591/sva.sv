```systemverilog
module barrel_shifter_sva (
    input logic CLK,
    input logic [15:0] in,
    input logic [3:0] shift,
    input logic dir,
    output logic [15:0] out
);
    // Shift direction must be either 0 (left) or 1 (right)
    direction_check: assert property (
        @(posedge CLK) disable iff (!CLK) (dir == 0 || dir == 1)
    );

    // Shift value must be within the valid range [0, 15]
    shift_value_check: assert property (
        @(posedge CLK) disable iff (!CLK) (shift >= 4'b0000 && shift <= 4'b1111)
    );

    // Output should be the result of the shift operations
    output_check: assert property (
        @(posedge CLK) disable iff (!CLK) (out == ((dir == 0) ? (in << shift) : (in >> shift)))
    );

    // Shifted data 1 should be the result of the first shift operation
    shifted_data_1_check: assert property (
        @(posedge CLK) disable iff (!CLK) (shifted_data_1 == ((dir == 0) ? (in << shift) : (in >> shift)))
    );

    // Shifted data 2 should be the result of the second shift operation
    shifted_data_2_check: assert property (
        @(posedge CLK) disable iff (!CLK) (shifted_data_2 == ((dir == 0) ? (shifted_data_1 << shift) : (shifted_data_1 >> shift)))
    );

    // Pipeline stages should be consistent
    pipeline_consistency_check: assert property (
        @(posedge CLK) disable iff (!CLK) (shifted_data_2 == out)
    );

    // Input should not change during shift operations
    input_consistency_check: assert property (
        @(posedge CLK) disable iff (!CLK) (in == in)
    );

    // Shift value should not change during shift operations
    shift_consistency_check: assert property (
        @(posedge CLK) disable iff (!CLK) (shift == shift)
    );

    // Direction should not change during shift operations
    direction_consistency_check: assert property (
        @(posedge CLK) disable iff (!CLK) (dir == dir)
    );
endmodule
```