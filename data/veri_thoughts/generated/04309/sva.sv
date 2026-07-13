module controllerHdl_Wrap_2pi_assertions (
    input logic clk,
    input logic signed [18:0] x,
    input logic signed [17:0] wrap
);

    // Sampled on external clk because the RTL is combinational and has no reset.
    localparam logic signed [18:0] TWO_PI     = 19'sb0011001001000100000;
    localparam logic signed [19:0] TWO_PI_EXT = 20'sb00011001001000100000;

    // Output matches the RTL's full conditional datapath.
    check_full_wrap_function: assert property (
        @(posedge clk)
        wrap == (
            (x >= TWO_PI) ? logic signed [17:0]'($signed({x[18], x}) - TWO_PI_EXT) :
            ((x < 19'sd0) ? logic signed [17:0]'($signed({x[18], x}) + TWO_PI_EXT) :
                            logic signed [17:0]'(x))
        )
    );

    // Negative inputs take the add-constant path.
    check_negative_input_adds_two_pi: assert property (
        @(posedge clk)
        (x < 19'sd0) |-> (wrap == logic signed [17:0]'($signed({x[18], x}) + TWO_PI_EXT))
    );

    // Non-negative inputs below the constant pass through unchanged.
    check_midrange_input_passthrough: assert property (
        @(posedge clk)
        ((x >= 19'sd0) && (x < TWO_PI)) |-> (wrap == logic signed [17:0]'(x))
    );

    // Inputs at or above the constant take the subtract-constant path.
    check_large_input_subtracts_two_pi: assert property (
        @(posedge clk)
        (x >= TWO_PI) |-> (wrap == logic signed [17:0]'($signed({x[18], x}) - TWO_PI_EXT))
    );

    // Zero maps directly to zero.
    check_zero_maps_to_zero: assert property (
        @(posedge clk)
        (x == 19'sd0) |-> (wrap == 18'sd0)
    );

    // The constant itself maps to zero after one subtraction.
    check_two_pi_maps_to_zero: assert property (
        @(posedge clk)
        (x == TWO_PI) |-> (wrap == 18'sd0)
    );

    // Negative of the constant maps to zero after one addition.
    check_minus_two_pi_maps_to_zero: assert property (
        @(posedge clk)
        (x == -TWO_PI) |-> (wrap == 18'sd0)
    );

endmodule