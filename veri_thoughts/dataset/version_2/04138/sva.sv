module barrel_shifter_assertions #(
    parameter width = 8,
    parameter log2width = 3
) (
    input logic clk,
    input logic [width-1:0] in,
    input logic [log2width-1:0] shift,
    input logic [width-1:0] out
);

    // Sampling clock is external; the RTL itself has no clock or reset.
    // DUT behavior is purely combinational: out is the left-shifted input.

    // Output must always match the RTL shift expression.
    check_functional_shift: assert property (
        @(posedge clk) out == ((shift == '0) ? in : (in << shift))
    );

    // A zero shift passes the input through unchanged.
    check_zero_shift_passthrough: assert property (
        @(posedge clk) (shift == '0) |-> (out == in)
    );

    // A zero input must produce a zero output.
    check_zero_input_zero_output: assert property (
        @(posedge clk) (in == '0) |-> (out == '0)
    );

    // Any non-zero left shift forces the least-significant output bit low.
    check_nonzero_shift_lsb_zero: assert property (
        @(posedge clk) (shift != '0) |-> (out[0] == 1'b0)
    );

    // For in-range shifts, the output MSB comes from the corresponding input bit.
    check_msb_source_bit: assert property (
        @(posedge clk) (shift < width) |-> (out[width-1] == in[width-1-shift])
    );

    // Shifts at or beyond the data width must zero the output.
    check_large_shift_zero_output: assert property (
        @(posedge clk) (shift >= width) |-> (out == '0)
    );

    generate
        if (width > 1) begin : gen_shift_by_one
            // A shift of one matches an explicit one-bit left shift.
            check_shift_by_one: assert property (
                @(posedge clk) (shift == 1) |-> (out == {in[width-2:0], 1'b0})
            );
        end
        if ((width > 2) && (log2width > 1)) begin : gen_shift_by_two
            // A shift of two matches an explicit two-bit left shift.
            check_shift_by_two: assert property (
                @(posedge clk) (shift == 2) |-> (out == {in[width-3:0], 2'b00})
            );
        end
    endgenerate

endmodule