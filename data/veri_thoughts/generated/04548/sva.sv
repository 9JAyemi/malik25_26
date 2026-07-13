module binary_to_gray_sva (
    input logic        clk,
    input logic [7:0]  binary_in,
    input logic        sel_b1,
    input logic        sel_b2,
    input logic [7:0]  gray_out
);

    // No DUT clock or reset exists; sample this combinational logic on clk.
    // The internal pos calculation is unused at the output.

    // gray_out must match the implemented mux expression every cycle.
    check_output_function: assert property (
        @(posedge clk)
        gray_out == (sel_b1 ? binary_in : (sel_b2 ? {1'b0, binary_in[7:1]} : binary_in))
    );

    // sel_b1 selects the direct binary input.
    check_sel_b1_passthrough: assert property (
        @(posedge clk)
        sel_b1 |-> (gray_out == binary_in)
    );

    // With only sel_b2 asserted, gray_out is binary_in shifted right by 1.
    check_shift_right_selected: assert property (
        @(posedge clk)
        (!sel_b1 && sel_b2) |-> (gray_out == {1'b0, binary_in[7:1]})
    );

    // With both selects low, gray_out passes binary_in unchanged.
    check_default_passthrough: assert property (
        @(posedge clk)
        (!sel_b1 && !sel_b2) |-> (gray_out == binary_in)
    );

    // sel_b1 has priority over sel_b2 when both are high.
    check_sel_b1_priority: assert property (
        @(posedge clk)
        (sel_b1 && sel_b2) |-> (gray_out == binary_in)
    );

    // The shifted path forces the MSB of gray_out low.
    check_shifted_msb_zero: assert property (
        @(posedge clk)
        (!sel_b1 && sel_b2) |-> (gray_out[7] == 1'b0)
    );

    // Stable inputs must keep the combinational output stable at sampled edges.
    check_stable_inputs_stable_output: assert property (
        @(posedge clk)
        $stable({binary_in, sel_b1, sel_b2}) |-> $stable(gray_out)
    );

endmodule