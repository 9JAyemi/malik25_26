module bitwise_and_sva (
    input logic        clk,
    input logic [15:0] data_in,
    input logic [15:0] mask,
    input logic        enable,
    input logic [15:0] data_out
);

    // data_out must always match the DUT's combinational function.
    check_bitwise_and_function: assert property (
        @(posedge clk) data_out == (enable ? (data_in & mask) : data_in)
    );

    // When disabled, data_out must pass data_in through unchanged.
    check_bypass_when_disabled: assert property (
        @(posedge clk) !enable |-> (data_out == data_in)
    );

    // When enabled, data_out must equal data_in masked by mask.
    check_mask_when_enabled: assert property (
        @(posedge clk) enable |-> (data_out == (data_in & mask))
    );

    // With a zero mask and enable high, all output bits must be zero.
    check_zero_mask_clears_output: assert property (
        @(posedge clk) enable && (mask == 16'h0000) |-> (data_out == 16'h0000)
    );

    // With an all-ones mask and enable high, data_out must equal data_in.
    check_full_mask_passes_input: assert property (
        @(posedge clk) enable && (mask == 16'hFFFF) |-> (data_out == data_in)
    );

    // When enabled, data_out cannot assert bits that are masked off.
    check_mask_blocks_cleared_bits: assert property (
        @(posedge clk) enable |-> ((data_out & ~mask) == 16'h0000)
    );

endmodule