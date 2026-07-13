module top_module_sva (
    input logic       clk,
    input logic       reset,
    input logic [3:0] signed_mag,
    input logic       select,
    input logic [7:0] q,
    input logic [3:0] counter_out,
    input logic [3:0] converter_out,
    input logic [7:0] functional_out
);

    // q continuously mirrors the internal functional_out register.
    check_q_matches_functional_out: assert property (
        @(posedge clk) disable iff (reset) (q == functional_out)
    );

    // Reset clears the internal registered output.
    check_functional_out_reset_zero: assert property (
        @(posedge clk) reset |=> (functional_out == 8'b0)
    );

    // Reset drives the top-level output to zero.
    check_q_reset_zero: assert property (
        @(posedge clk) reset |=> (q == 8'b0)
    );

    // Reset clears the binary counter.
    check_counter_reset_zero: assert property (
        @(posedge clk) reset |=> (counter_out == 4'b0)
    );

    // The counter increments by one on each active cycle.
    check_counter_increments: assert property (
        @(posedge clk) disable iff (reset) 1'b1 |=> (counter_out == ($past(counter_out) + 4'd1))
    );

    // Non-negative signed_mag values pass through unchanged.
    check_converter_positive_passthrough: assert property (
        @(posedge clk) disable iff (reset) (!signed_mag[3]) |-> (converter_out == signed_mag)
    );

    // Negative signed_mag values follow the implemented complement formula.
    check_converter_negative_formula: assert property (
        @(posedge clk) disable iff (reset) signed_mag[3] |-> (converter_out == ~(signed_mag - 4'd1))
    );

    // select=1 causes functional_out to capture the counter value.
    check_functional_out_selects_counter: assert property (
        @(posedge clk) disable iff (reset) select |=> (functional_out == {4'b0, $past(counter_out)})
    );

    // select=0 causes functional_out to capture the converter value.
    check_functional_out_selects_converter: assert property (
        @(posedge clk) disable iff (reset) (!select) |=> (functional_out == {4'b0, $past(converter_out)})
    );

    // The upper nibble of q is always zero in normal operation.
    check_q_upper_nibble_zero: assert property (
        @(posedge clk) disable iff (reset) (q[7:4] == 4'b0)
    );

endmodule