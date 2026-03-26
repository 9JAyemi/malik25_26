module boolean_func_sva (
    input logic clk,
    input logic a,
    input logic b,
    input logic c,
    input logic z
);

    // z matches the RTL boolean expression.
    check_output_equation: assert property (
        @(posedge clk) z == ((a & b) ^ (c | ~b))
    );

    // When b is low, z is always high.
    check_b_low_forces_z_high: assert property (
        @(posedge clk) !b |-> (z == 1'b1)
    );

    // When b is high, z reduces to a XOR c.
    check_b_high_reduces_to_xor: assert property (
        @(posedge clk) b |-> (z == (a ^ c))
    );

    // With b high and equal inputs, z is low.
    check_b_high_equal_inputs_drive_low: assert property (
        @(posedge clk) (b && (a == c)) |-> (z == 1'b0)
    );

    // With b high and different inputs, z is high.
    check_b_high_different_inputs_drive_high: assert property (
        @(posedge clk) (b && (a != c)) |-> (z == 1'b1)
    );

    // z can be low only when b is high and a equals c.
    check_low_output_condition: assert property (
        @(posedge clk) !z |-> (b && (a == c))
    );

endmodule