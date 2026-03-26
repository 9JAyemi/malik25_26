module top_module_sva (
    input logic        clk,
    input logic [7:0]  in1,
    input logic [7:0]  in2,
    input logic        sel,
    input logic [7:0]  sum
);

    // Sum must match the selected top-level datapath.
    check_sum_selected_function: assert property (
        @(posedge clk) sum == (sel ? in2 : (in1 ^ in2))
    );

    // When sel is high, the output must route in2.
    check_sel_high_routes_in2: assert property (
        @(posedge clk) sel |-> (sum == in2)
    );

    // When sel is low, the output must be the bitwise XOR path.
    check_sel_low_routes_bitwise_xor: assert property (
        @(posedge clk) !sel |-> (sum == (in1 ^ in2))
    );

    // Equal inputs on the XOR path must produce zero.
    check_sel_low_equal_inputs_zero: assert property (
        @(posedge clk) (!sel && (in1 == in2)) |-> (sum == 8'h00)
    );

    // Zero on in2 must pass in1 through the XOR path.
    check_sel_low_in2_zero_passthrough: assert property (
        @(posedge clk) (!sel && (in2 == 8'h00)) |-> (sum == in1)
    );

    // Zero on in1 must pass in2 through the XOR path.
    check_sel_low_in1_zero_passthrough: assert property (
        @(posedge clk) (!sel && (in1 == 8'h00)) |-> (sum == in2)
    );

    // All ones on in2 must invert in1 on the XOR path.
    check_sel_low_in2_ones_inverts_in1: assert property (
        @(posedge clk) (!sel && (in2 == 8'hFF)) |-> (sum == ~in1)
    );

endmodule