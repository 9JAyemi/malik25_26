module top_module_sva (
    input logic clk,
    input logic reset,                  // Synchronous active-high reset
    input logic [3:0] signed_mag,       // 4-bit input for the signed magnitude converter
    input logic select,                 // Select input to choose between counter and converter
    input logic [7:0] q,                // 8-bit output from the functional module
    input logic [3:0] counter_out,      // Internal counter output
    input logic [3:0] converter_out     // Internal converter output
);

    ///// Reset behavior /////
    // On reset, counter_out is cleared to 0.
    reset_clears_counter: assert property (
        @(posedge clk) reset |-> (counter_out == 4'b0000)
    );
    // On reset, converter_out is cleared to 0.
    reset_clears_converter: assert property (
        @(posedge clk) reset |-> (converter_out == 4'b0000)
    );
    // On reset, q is cleared to 0.
    reset_clears_q: assert property (
        @(posedge clk) reset |-> (q == 8'b00000000)
    );

    ///// Counter behavior /////
    // Counter increments by 1 on each non-reset cycle.
    counter_increments: assert property (
        @(posedge clk) disable iff (reset) 1'b1 |=> (counter_out == ($past(counter_out) + 4'd1))
    );
    // Counter wraps from 15 back to 0.
    counter_wraps_from_15: assert property (
        @(posedge clk) disable iff (reset) (counter_out == 4'hF) |=> (counter_out == 4'h0)
    );

    ///// Converter behavior /////
    // Converter output equals 2's complement of signed_mag when signed_mag[3] is 1.
    converter_twos_comp_when_negative: assert property (
        @(posedge clk) disable iff (reset) signed_mag[3] |-> (converter_out == (~signed_mag + 4'd1))
    );
    // Converter output equals signed_mag when signed_mag[3] is 0.
    converter_pass_through_when_positive: assert property (
        @(posedge clk) disable iff (reset) !signed_mag[3] |-> (converter_out == signed_mag)
    );

    ///// Output selection /////
    // When select is HIGH, q reflects the zero-extended counter value.
    q_selects_counter: assert property (
        @(posedge clk) disable iff (reset) select |-> (q == {4'b0000, counter_out})
    );
    // When select is LOW, q reflects the zero-extended converter value.
    q_selects_converter: assert property (
        @(posedge clk) disable iff (reset) !select |-> (q == {4'b0000, converter_out})
    );

    ///// Output consistency /////
    // q always has its upper nibble at 0.
    q_upper_nibble_zero: assert property (
        @(posedge clk) disable iff (reset) (q[7:4] == 4'b0000)
    );

endmodule