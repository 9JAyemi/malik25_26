module mux_2_1_sva (
    input logic clk,
    input logic sel,
    input logic in0,
    input logic in1,
    input logic out
);

// Output matches the RTL AND/OR equation.
    check_function_equation: assert property (
        @(posedge clk) out == ((~sel & in0) | (sel & in1))
    );

// When sel is low, out follows in0.
    check_sel_low_routes_in0: assert property (
        @(posedge clk) !sel |-> (out == in0)
    );

// When sel is high, out follows in1.
    check_sel_high_routes_in1: assert property (
        @(posedge clk) sel |-> (out == in1)
    );

// If both inputs are low, out must be low.
    check_both_inputs_low_drive_out_low: assert property (
        @(posedge clk) (!in0 && !in1) |-> (!out)
    );

// If both inputs are high, out must be high.
    check_both_inputs_high_drive_out_high: assert property (
        @(posedge clk) (in0 && in1) |-> (out)
    );

// A high output requires at least one high input.
    check_out_high_requires_some_high_input: assert property (
        @(posedge clk) out |-> (in0 || in1)
    );

// A low output requires both inputs to be low.
    check_out_low_requires_both_low: assert property (
        @(posedge clk) !out |-> (!in0 && !in1)
    );

endmodule
