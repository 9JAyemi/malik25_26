module top_module_sva (
    input logic clk,
    input logic [15:0] in,
    input logic [7:0] out_hi,
    input logic [7:0] out_lo
);

// out_hi captures the previous cycle's upper byte.
    check_out_hi_captures_upper_byte: assert property (
        @(posedge clk) 1'b1 |=> (out_hi == $past(in[15:8]))
    );

// out_lo captures the previous cycle's lower byte.
    check_out_lo_captures_lower_byte: assert property (
        @(posedge clk) 1'b1 |=> (out_lo == $past(in[7:0]))
    );

// The full 16-bit output vector matches the previous cycle's input.
    check_out_vector_captures_input: assert property (
        @(posedge clk) 1'b1 |=> ({out_hi, out_lo} == $past(in))
    );

endmodule
