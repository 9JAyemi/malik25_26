module top_module_assertions(
    input logic clk,
    input logic a,
    input logic b,
    input logic c,
    input logic w,
    input logic x,
    input logic y,
    input logic z,
    input logic out
);

    // w directly mirrors input a.
    check_w_passthrough: assert property (
        @(posedge clk) w == a
    );

    // x directly mirrors input b.
    check_x_passthrough: assert property (
        @(posedge clk) x == b
    );

    // y directly mirrors input c.
    check_y_passthrough: assert property (
        @(posedge clk) y == c
    );

    // z is the AND of a and b.
    check_z_and_function: assert property (
        @(posedge clk) z == (a & b)
    );

    // z is consistent with the mirrored outputs w and x.
    check_z_matches_w_and_x: assert property (
        @(posedge clk) z == (w & x)
    );

    // A true sampled function drives out high on the next cycle.
    check_out_set_on_function_true: assert property (
        @(posedge clk) ((a ^ b) & a & c) |=> out
    );

    // A false sampled function drives out low on the next cycle.
    check_out_clear_on_function_false: assert property (
        @(posedge clk) !((a ^ b) & a & c) |=> !out
    );

endmodule