module top_module_sva (
    input logic clk,
    input logic reset, // synchronous active-high
    input logic [3:0] counter_out,
    input logic [3:0] encoder_in,
    input logic [1:0] encoder_out,
    input logic [3:0] and_out
);

    ///// Counter behavior /////
    // After any cycle with reset asserted, counter_out is 0 on the next cycle.
    counter_clears_after_reset: assert property (
        @(posedge clk) disable iff (reset) $past(reset) |-> (counter_out == 4'b0000)
    );

    // When not in or coming from reset, counter_out increments by 1 modulo 16 each cycle.
    counter_increments_when_no_reset: assert property (
        @(posedge clk) disable iff (reset) !$past(reset) |-> (counter_out == ($past(counter_out) + 4'd1))
    );

    // Explicit wrap from 4'hF to 4'h0 when no reset.
    counter_wraps_from_F_to_0: assert property (
        @(posedge clk) disable iff (reset) (!$past(reset) && ($past(counter_out) == 4'hF)) |-> (counter_out == 4'h0)
    );

    ///// Priority encoder mapping /////
    // encoder_in 0001 -> encoder_out 00.
    encoder_map_0001: assert property (
        @(posedge clk) disable iff (reset) (encoder_in == 4'b0001) |-> (encoder_out == 2'b00)
    );

    // encoder_in 0010 -> encoder_out 01.
    encoder_map_0010: assert property (
        @(posedge clk) disable iff (reset) (encoder_in == 4'b0010) |-> (encoder_out == 2'b01)
    );

    // encoder_in 0100 -> encoder_out 10.
    encoder_map_0100: assert property (
        @(posedge clk) disable iff (reset) (encoder_in == 4'b0100) |-> (encoder_out == 2'b10)
    );

    // encoder_in 1000 -> encoder_out 11.
    encoder_map_1000: assert property (
        @(posedge clk) disable iff (reset) (encoder_in == 4'b1000) |-> (encoder_out == 2'b11)
    );

    // For any non-listed pattern, encoder_out is 00 (default case).
    encoder_map_default_otherwise_00: assert property (
        @(posedge clk) disable iff (reset)
            ((encoder_in != 4'b0001) && (encoder_in != 4'b0010) && (encoder_in != 4'b0100) && (encoder_in != 4'b1000))
            |-> (encoder_out == 2'b00)
    );

    ///// AND output behavior /////
    // and_out equals counter_out AND {2'b00, encoder_out}.
    and_out_matches_spec: assert property (
        @(posedge clk) disable iff (reset) (and_out == {2'b00, (counter_out[1:0] & encoder_out)})
    );

    // Upper two bits of and_out are always zero.
    and_out_upper_bits_zero: assert property (
        @(posedge clk) disable iff (reset) (and_out[3:2] == 2'b00)
    );

endmodule