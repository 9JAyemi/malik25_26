module value_converter_sva (
    // DUT ports
    input logic [3:0] input_val,
    input logic [2:0] output_val,
    // Sampling clock for SVA (DUT has no clock/reset; purely combinational)
    input logic clk
);
    // Output equals 7 for input 5 or 6; else equals input[2:0].
    check_output_functional_mapping: assert property (
        @(posedge clk) output_val == (((input_val == 4'd5) || (input_val == 4'd6)) ? 3'd7 : input_val[2:0])
    );

    // When input is 5 or 6, output must be 7.
    check_special_cases_to_7: assert property (
        @(posedge clk) ((input_val == 4'd5) || (input_val == 4'd6)) |-> (output_val == 3'd7)
    );

    // For inputs other than 5 or 6, output must equal input[2:0].
    check_default_passthrough: assert property (
        @(posedge clk) !((input_val == 4'd5) || (input_val == 4'd6)) |-> (output_val == input_val[2:0])
    );
endmodule