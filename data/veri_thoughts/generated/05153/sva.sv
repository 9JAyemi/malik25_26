module data_buffer_sva (
    input logic clk,
    input logic [7:0] A,
    input logic [15:0] Z,
    input logic TE_B,
    input logic VPB,
    input logic VPWR,
    input logic VGND,
    input logic VNB
);

    // When enabled, Z is A in the upper byte and zero in the lower byte.
    check_enabled_mapping: assert property (
        @(posedge clk) TE_B |-> (Z == {A, 8'h00})
    );

    // When disabled, Z is driven to zero.
    check_disabled_zero: assert property (
        @(posedge clk) !TE_B |-> (Z == 16'h0000)
    );

    // The upper byte of Z matches A whenever the buffer is enabled.
    check_enabled_upper_byte_matches_a: assert property (
        @(posedge clk) TE_B |-> (Z[15:8] == A)
    );

    // The lower byte of Z is always zero.
    check_lower_byte_always_zero: assert property (
        @(posedge clk) Z[7:0] == 8'h00
    );

    // A rising enable produces the enabled output mapping.
    check_enable_rise_sets_output: assert property (
        @(posedge clk) $rose(TE_B) |-> (Z == {A, 8'h00})
    );

    // A falling enable clears the output.
    check_enable_fall_clears_output: assert property (
        @(posedge clk) $fell(TE_B) |-> (Z == 16'h0000)
    );

endmodule