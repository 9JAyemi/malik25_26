module bool_func_sva (
    // DUT ports
    input logic x,
    input logic y,
    input logic z,
    input logic f,
    // Sampling clock for assertions (DUT has no clock/reset)
    input logic clk
);
    // Analysis: DUT is purely combinational; no clock/reset; f = (x|y) & (x^z).
    // Local mirrors of DUT's internal wires for readability
    wire x_or_y  = x | y;
    wire x_xor_z = x ^ z;

    // f must equal (x|y) & (x^z)
    check_functional_equation: assert property (
        @(posedge clk) f == (x_or_y & x_xor_z)
    );

    // If x == z, then f must be 0 (since x^z == 0)
    check_zero_when_x_eq_z: assert property (
        @(posedge clk) (x == z) |-> (f == 1'b0)
    );

    // If x|y == 0, then f must be 0
    check_zero_when_or_zero: assert property (
        @(posedge clk) (x_or_y == 1'b0) |-> (f == 1'b0)
    );

    // If x^z == 0, then f must be 0
    check_zero_when_xor_zero: assert property (
        @(posedge clk) (x_xor_z == 1'b0) |-> (f == 1'b0)
    );

    // If both terms are 1, f must be 1
    check_one_when_terms_one: assert property (
        @(posedge clk) (x_xor_z && x_or_y) |-> (f == 1'b1)
    );

    // When x=0 and z=1, f equals y
    check_passthrough_y_when_x0z1: assert property (
        @(posedge clk) ((x == 1'b0) && (z == 1'b1)) |-> (f == y)
    );

    // When x=1 and z=0, f is 1 regardless of y
    check_one_when_x1z0: assert property (
        @(posedge clk) ((x == 1'b1) && (z == 1'b0)) |-> (f == 1'b1)
    );

    // When x=0 and z=0, f is 0
    check_zero_when_x0z0: assert property (
        @(posedge clk) ((x == 1'b0) && (z == 1'b0)) |-> (f == 1'b0)
    );

    // When x=1 and z=1, f is 0
    check_zero_when_x1z1: assert property (
        @(posedge clk) ((x == 1'b1) && (z == 1'b1)) |-> (f == 1'b0)
    );

    // When x=0 and y=0, f is 0
    check_zero_when_x0y0: assert property (
        @(posedge clk) ((x == 1'b0) && (y == 1'b0)) |-> (f == 1'b0)
    );
endmodule