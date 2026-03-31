module split_16bit_input_sva (
    input logic clk,
    input logic [15:0] in,
    input logic [7:0] out_hi,
    input logic [7:0] out_lo
);

    // out_hi captures the upper byte of in on the previous clock.
    check_out_hi_captures_upper_byte: assert property (
        @(posedge clk) 1'b1 |=> (out_hi == $past(in[15:8]))
    );

    // out_lo captures the lower byte of in on the previous clock.
    check_out_lo_captures_lower_byte: assert property (
        @(posedge clk) 1'b1 |=> (out_lo == $past(in[7:0]))
    );

    // The full output bus matches the previous cycle's input bytes.
    check_output_bus_matches_previous_input: assert property (
        @(posedge clk) 1'b1 |=> ({out_hi, out_lo} == $past({in[15:8], in[7:0]}))
    );

endmodule

module top_module_sva (
    input logic clk,
    input logic [15:0] in,
    input logic [7:0] out_hi,
    input logic [7:0] out_lo
);

    // out_hi captures the upper byte of in on the previous clock.
    check_out_hi_captures_upper_byte: assert property (
        @(posedge clk) 1'b1 |=> (out_hi == $past(in[15:8]))
    );

    // out_lo captures the lower byte of in on the previous clock.
    check_out_lo_captures_lower_byte: assert property (
        @(posedge clk) 1'b1 |=> (out_lo == $past(in[7:0]))
    );

    // The full output bus matches the previous cycle's input bytes.
    check_output_bus_matches_previous_input: assert property (
        @(posedge clk) 1'b1 |=> ({out_hi, out_lo} == $past({in[15:8], in[7:0]}))
    );

endmodule