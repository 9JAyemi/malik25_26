module butterfly_unit_sva (
    input logic       clk,
    input logic [1:0] x_real,
    input logic [1:0] x_imag,
    input logic [1:0] y_real,
    input logic [1:0] y_imag,
    input logic [1:0] z_real,
    input logic [1:0] z_imag
);

    // z_real is the 2-bit sum of x_real and y_real.
    check_z_real_sum: assert property (
        @(posedge clk) z_real == (x_real + y_real)
    );

    // z_imag is the 2-bit sum of x_imag and y_imag.
    check_z_imag_sum: assert property (
        @(posedge clk) z_imag == (x_imag + y_imag)
    );

    // A zero x_real operand passes y_real through to z_real.
    check_z_real_x_zero_passthrough: assert property (
        @(posedge clk) (x_real == 2'b00) |-> (z_real == y_real)
    );

    // A zero y_real operand passes x_real through to z_real.
    check_z_real_y_zero_passthrough: assert property (
        @(posedge clk) (y_real == 2'b00) |-> (z_real == x_real)
    );

    // A zero x_imag operand passes y_imag through to z_imag.
    check_z_imag_x_zero_passthrough: assert property (
        @(posedge clk) (x_imag == 2'b00) |-> (z_imag == y_imag)
    );

    // A zero y_imag operand passes x_imag through to z_imag.
    check_z_imag_y_zero_passthrough: assert property (
        @(posedge clk) (y_imag == 2'b00) |-> (z_imag == x_imag)
    );

    // z_real stays unchanged when its real inputs stay unchanged.
    check_z_real_stable_when_inputs_stable: assert property (
        @(posedge clk) !$initstate && $stable(x_real) && $stable(y_real) |-> $stable(z_real)
    );

    // z_imag stays unchanged when its imag inputs stay unchanged.
    check_z_imag_stable_when_inputs_stable: assert property (
        @(posedge clk) !$initstate && $stable(x_imag) && $stable(y_imag) |-> $stable(z_imag)
    );

endmodule