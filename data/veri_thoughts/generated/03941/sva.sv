module simple_circuit_sva (
    input logic clk,
    input logic [3:0] in_value,
    input logic [2:0] out_value
);

    // Output matches the implemented combinational function.
    check_exact_function: assert property (
        @(posedge clk) disable iff (1'b0)
        out_value == ((in_value <= 4'd7) ? in_value[2:0] : 3'b111)
    );

    // Inputs 0 through 7 pass their low three bits to the output.
    check_low_range_passthrough: assert property (
        @(posedge clk) disable iff (1'b0)
        (in_value <= 4'd7) |-> (out_value == in_value[2:0])
    );

    // Inputs above 7 force the output to 3'b111.
    check_high_range_saturation: assert property (
        @(posedge clk) disable iff (1'b0)
        (in_value > 4'd7) |-> (out_value == 3'b111)
    );

endmodule