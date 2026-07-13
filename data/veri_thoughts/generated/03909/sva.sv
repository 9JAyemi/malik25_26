module mux_4_1_enable_sva (
    input logic [3:0]  MUX_INPUTS,
    input logic [1:0]  MUX_SELECT,
    input logic        EN,
    input logic [31:0] MUX_OUTPUT
);

    // Output is always zero-extended above bit 0.
    check_output_upper_bits_zero: assert property (
        @($global_clock) (MUX_OUTPUT[31:1] == 31'h00000000)
    );

    // Disabled mux drives all zeros.
    check_disabled_drives_zero: assert property (
        @($global_clock) (!EN) |-> (MUX_OUTPUT == 32'h00000000)
    );

    // Enabled select 00 forwards input bit 0.
    check_select_00_maps_input0: assert property (
        @($global_clock) (EN && (MUX_SELECT == 2'b00)) |-> (MUX_OUTPUT == {{31{1'b0}}, MUX_INPUTS[0]})
    );

    // Enabled select 01 forwards input bit 1.
    check_select_01_maps_input1: assert property (
        @($global_clock) (EN && (MUX_SELECT == 2'b01)) |-> (MUX_OUTPUT == {{31{1'b0}}, MUX_INPUTS[1]})
    );

    // Enabled select 10 forwards input bit 3.
    check_select_10_maps_input3: assert property (
        @($global_clock) (EN && (MUX_SELECT == 2'b10)) |-> (MUX_OUTPUT == {{31{1'b0}}, MUX_INPUTS[3]})
    );

    // Enabled select 11 forwards input bit 3.
    check_select_11_maps_input3: assert property (
        @($global_clock) (EN && (MUX_SELECT == 2'b11)) |-> (MUX_OUTPUT == {{31{1'b0}}, MUX_INPUTS[3]})
    );

endmodule