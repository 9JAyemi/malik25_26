module bitwise_and_mask_sva (
    input logic [31:0] data_in,
    input logic        enable,
    input logic [31:0] data_out
);
    // Analysis: no clock/reset; purely combinational mask. Assertions sample on enable edges.
    // Function: data_out = enable ? (data_in & 32'hFFFF0000) : 32'd0.

    // When enable rises, data_out equals data_in masked to upper 16 bits.
    check_mask_when_enabled: assert property (
        @(posedge enable) ##0 (data_out == (data_in & 32'hFFFF0000))
    );

    // When enable falls, data_out becomes zero.
    check_zero_when_disabled: assert property (
        @(negedge enable) ##0 (data_out == 32'd0)
    );

    // Lower 16 bits are always zero on any enable edge.
    check_lower_bits_zero: assert property (
        @(posedge enable or negedge enable) ##0 (data_out[15:0] == 16'd0)
    );

    // When enabled, upper 16 bits pass through from data_in.
    check_upper_bits_passthrough_when_enabled: assert property (
        @(posedge enable) ##0 (data_out[31:16] == data_in[31:16])
    );

    // When disabled, upper 16 bits are zero.
    check_upper_bits_zero_when_disabled: assert property (
        @(negedge enable) ##0 (data_out[31:16] == 16'd0)
    );

endmodule