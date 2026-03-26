module inv_module_sva (
    input logic clk,
    input logic [3:0] data_in,
    input logic enable,
    input logic [3:0] data_out
);

    // Output must implement the selected invert or pass-through function.
    check_output_function: assert property (
        @(posedge clk) data_out == (enable ? ~data_in : data_in)
    );

    // When enable is low, output must pass input through unchanged.
    check_passthrough_when_disabled: assert property (
        @(posedge clk) !enable |-> (data_out == data_in)
    );

    // When enable is high, output must be the bitwise inverse of input.
    check_invert_when_enabled: assert property (
        @(posedge clk) enable |-> (data_out == ~data_in)
    );

    // Bit 0 must follow the selected function.
    check_bit0_function: assert property (
        @(posedge clk) data_out[0] == (enable ? ~data_in[0] : data_in[0])
    );

    // Bit 1 must follow the selected function.
    check_bit1_function: assert property (
        @(posedge clk) data_out[1] == (enable ? ~data_in[1] : data_in[1])
    );

    // Bit 2 must follow the selected function.
    check_bit2_function: assert property (
        @(posedge clk) data_out[2] == (enable ? ~data_in[2] : data_in[2])
    );

    // Bit 3 must follow the selected function.
    check_bit3_function: assert property (
        @(posedge clk) data_out[3] == (enable ? ~data_in[3] : data_in[3])
    );

endmodule