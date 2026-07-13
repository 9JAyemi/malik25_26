module mux_2_1_sva (
    input logic clk,
    input logic sel,
    input logic in0,
    input logic in1,
    input logic out
);

    // Output matches the implemented mux equation.
    check_mux_equation: assert property (
        @(posedge clk) out == ((~sel & in0) | (sel & in1))
    );

    // When sel is low, the output follows in0.
    check_sel_low_routes_in0: assert property (
        @(posedge clk) (sel == 1'b0) |-> (out == in0)
    );

    // When sel is high, the output follows in1.
    check_sel_high_routes_in1: assert property (
        @(posedge clk) (sel == 1'b1) |-> (out == in1)
    );

    // A low output can only come from both inputs being low.
    check_out_low_requires_both_inputs_low: assert property (
        @(posedge clk) (out == 1'b0) |-> ((in0 == 1'b0) && (in1 == 1'b0))
    );

    // A high output must come from at least one high input.
    check_out_high_requires_one_input_high: assert property (
        @(posedge clk) (out == 1'b1) |-> ((in0 == 1'b1) || (in1 == 1'b1))
    );

endmodule