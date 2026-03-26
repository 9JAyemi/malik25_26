module top_module_sva (
    input logic        clk,
    input logic [15:0] in,
    input logic [7:0]  out_hi,
    input logic [7:0]  out_lo
);

    // External sampling clock; the RTL itself has no clock or reset.

    // out_hi always reflects the upper byte of in.
    check_out_hi_upper_byte: assert property (
        @(posedge clk) disable iff (1'b0) out_hi == in[15:8]
    );

    // out_lo follows the lower byte when that byte is nonzero.
    check_out_lo_lower_byte_when_nonzero: assert property (
        @(posedge clk) disable iff (1'b0) (in[7:0] != 8'h00) |-> (out_lo == in[7:0])
    );

    // out_lo switches to the upper byte when the lower byte is zero.
    check_out_lo_upper_byte_when_low_zero: assert property (
        @(posedge clk) disable iff (1'b0) (in[7:0] == 8'h00) |-> (out_lo == in[15:8])
    );

    // out_lo matches out_hi whenever the lower byte is zero.
    check_out_lo_equals_out_hi_when_low_zero: assert property (
        @(posedge clk) disable iff (1'b0) (in[7:0] == 8'h00) |-> (out_lo == out_hi)
    );

    // out_lo implements the mux function exactly.
    check_out_lo_mux_function: assert property (
        @(posedge clk) disable iff (1'b0) out_lo == ((in[7:0] == 8'h00) ? in[15:8] : in[7:0])
    );

    // A zero input drives both outputs to zero.
    check_zero_input_zero_outputs: assert property (
        @(posedge clk) disable iff (1'b0) (in == 16'h0000) |-> ((out_hi == 8'h00) && (out_lo == 8'h00))
    );

endmodule