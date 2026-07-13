module slice_module_assertions (
    input logic        clk,
    input logic [17:0] Din,
    input logic [7:0]  Dout
);

    // Upper output bits are zero because a 1-bit select is assigned into an 8-bit vector.
    check_dout_upper_bits_zero: assert property (
        @(posedge clk) Dout[7:1] === 7'b0
    );

    // For valid selector values 0 through 9, Dout is the zero-extended selected input bit.
    check_valid_index_maps_selected_bit: assert property (
        @(posedge clk) (Din[7:0] <= 8'd9) |-> (Dout === {7'b0, Din[Din[7:0] + 32'd8]})
    );

    // A selector value of 0 picks Din[8].
    check_selector_zero_uses_bit8: assert property (
        @(posedge clk) (Din[7:0] === 8'd0) |-> (Dout === {7'b0, Din[8]})
    );

    // A selector value of 9 picks Din[17].
    check_selector_nine_uses_bit17: assert property (
        @(posedge clk) (Din[7:0] === 8'd9) |-> (Dout === {7'b0, Din[17]})
    );

    // If the sampled input is unchanged, the sampled output must also be unchanged.
    check_stable_input_keeps_output_stable: assert property (
        @(posedge clk) $stable(Din) |-> $stable(Dout)
    );

endmodule