module bitwise_logic_sva (
    input logic clk,
    input logic in1,
    input logic in2,
    input logic in3,
    input logic out1
);

    // out1 must implement (in1 & in2) | ~in3.
    check_output_equation: assert property (
        @(posedge clk) out1 == ((in1 & in2) | (~in3))
    );

    // A low in3 forces out1 high.
    check_in3_low_forces_out1_high: assert property (
        @(posedge clk) (in3 == 1'b0) |-> (out1 == 1'b1)
    );

    // With in3 high, out1 reduces to in1 & in2.
    check_in3_high_reduces_to_and: assert property (
        @(posedge clk) (in3 == 1'b1) |-> (out1 == (in1 & in2))
    );

    // Both data inputs high force out1 high.
    check_both_inputs_high_force_out1_high: assert property (
        @(posedge clk) ((in1 == 1'b1) && (in2 == 1'b1)) |-> (out1 == 1'b1)
    );

    // With in3 high, a low in1 forces out1 low.
    check_in3_high_and_in1_low_force_out1_low: assert property (
        @(posedge clk) ((in3 == 1'b1) && (in1 == 1'b0)) |-> (out1 == 1'b0)
    );

    // With in3 high, a low in2 forces out1 low.
    check_in3_high_and_in2_low_force_out1_low: assert property (
        @(posedge clk) ((in3 == 1'b1) && (in2 == 1'b0)) |-> (out1 == 1'b0)
    );

    // A low out1 can occur only when in3 is high and one input is low.
    check_low_output_characterization: assert property (
        @(posedge clk) (out1 == 1'b0) |-> ((in3 == 1'b1) && ((in1 == 1'b0) || (in2 == 1'b0)))
    );

    // If out1 is high while in3 is high, both inputs must be high.
    check_high_output_with_in3_high_requires_both_inputs: assert property (
        @(posedge clk) ((out1 == 1'b1) && (in3 == 1'b1)) |-> ((in1 == 1'b1) && (in2 == 1'b1))
    );

endmodule