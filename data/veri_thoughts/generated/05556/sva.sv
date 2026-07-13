module top_module_assertions (
    input logic        clk,
    input logic        reset,
    input logic [35:0] in,
    input logic [31:0] out
);

    // Reset clears the registered outputs on the next clock.
    check_reset_clears_output: assert property (
        @(posedge clk)
        reset |=> (out == 32'b0)
    );

    // The first active update after reset only reflects the low input nibble.
    check_first_active_cycle_after_reset: assert property (
        @(posedge clk) disable iff (reset)
        ($past(reset,2) && $past(!reset)) |->
        (out == {{28{1'b0}}, $past(in[3:0])})
    );

    // The top-level output matches the delayed low nibble OR the fall-detect mask.
    check_full_output_relation: assert property (
        @(posedge clk) disable iff (reset)
        ($past(!reset) && $past(!reset,2)) |->
        (out == ({{28{1'b0}}, $past(in[3:0])} |
                 ($past(in[35:4],2) & ~$past(in[35:4]))))
    );

    // Upper output bits are falling-edge detection of input bits [35:8].
    check_upper_bits_falling_edge_relation: assert property (
        @(posedge clk) disable iff (reset)
        ($past(!reset) && $past(!reset,2)) |->
        (out[31:4] == ($past(in[35:8],2) & ~$past(in[35:8])))
    );

    // With no falling edges on input bits [35:8], upper output bits stay low.
    check_upper_bits_zero_without_falls: assert property (
        @(posedge clk) disable iff (reset)
        ($past(!reset) && $past(!reset,2) &&
         (($past(in[35:8],2) & ~$past(in[35:8])) == 28'b0)) |->
        (out[31:4] == 28'b0)
    );

    // Lower output bits are the prior low nibble OR falls on input bits [7:4].
    check_lower_bits_or_relation: assert property (
        @(posedge clk) disable iff (reset)
        ($past(!reset) && $past(!reset,2)) |->
        (out[3:0] == ($past(in[3:0]) |
                      ($past(in[7:4],2) & ~$past(in[7:4]))))
    );

    // A stable low nibble with no falls on input bits [7:4] passes through unchanged.
    check_lower_bits_passthrough_without_falls: assert property (
        @(posedge clk) disable iff (reset)
        ($past(!reset) && $past(!reset,2) &&
         ($past(in[3:0],2) == $past(in[3:0])) &&
         (($past(in[7:4],2) & ~$past(in[7:4])) == 4'b0)) |->
        (out[3:0] == $past(in[3:0]))
    );

    // Falling edges on input bits [7:4] must appear in the lower output bits.
    check_lower_bits_include_falls: assert property (
        @(posedge clk) disable iff (reset)
        ($past(!reset) && $past(!reset,2)) |->
        ((out[3:0] & ($past(in[7:4],2) & ~$past(in[7:4]))) ==
         ($past(in[7:4],2) & ~$past(in[7:4])))
    );

endmodule