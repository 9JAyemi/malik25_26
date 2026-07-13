module edge_detection_sva (
    input logic clk,
    input logic [7:0] in,
    input logic [7:0] out
);
    // MSB of out is always 0.
    check_out_msb_zero: assert property (
        @(posedge clk) out[7] == 1'b0
    );

    // Out is always either zero or {0,in[7:1]}.
    check_out_two_values_only: assert property (
        @(posedge clk) (out == 8'h00) || (out == {1'b0, in[7:1]})
    );

    // If input changes since last cycle, out equals {0,in[7:1]}.
    check_shift_on_change: assert property (
        @(posedge clk) (in != $past(in)) |-> (out == {1'b0, in[7:1]})
    );

    // If input is unchanged since last cycle, out is zero.
    check_zero_on_no_change: assert property (
        @(posedge clk) (in == $past(in)) |-> (out == 8'h00)
    );

    // If out is non-zero, input must have changed.
    check_nonzero_out_implies_change: assert property (
        @(posedge clk) (out[6:0] != 7'b0) |-> (in != $past(in))
    );

    // On change, out[0] equals in[1].
    check_bit0_on_change: assert property (
        @(posedge clk) (in != $past(in)) |-> (out[0] == in[1])
    );

    // On change, out[6] equals in[7].
    check_bit6_on_change: assert property (
        @(posedge clk) (in != $past(in)) |-> (out[6] == in[7])
    );

    // Out never sets bits outside of {0,in[7:1]}.
    check_out_subset_of_shifted: assert property (
        @(posedge clk) ((out & ~{1'b0, in[7:1]}) == 8'h00)
    );

    // When no change, out[6:0] are zero.
    check_lowbits_zero_on_no_change: assert property (
        @(posedge clk) (in == $past(in)) |-> (out[6:0] == 7'b0)
    );

endmodule