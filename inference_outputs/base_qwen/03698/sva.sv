module top_module_sva (
    input logic CLK,
    input logic [3:0] binary_input,
    input logic [1:0] shift_amount,
    output logic [3:0] shifted_gray_code_output
);
    wire [3:0] gray_code_output;

    gray_code gray_code_inst (
        .in(binary_input),
        .out(gray_code_output)
    );

    barrel_shifter barrel_shifter_inst (
        .data(gray_code_output),
        .shift_amount(shift_amount),
        .result(shifted_gray_code_output)
    );

    // Ensure that the Gray code conversion is correct
    gray_code_conversion: assert property (
        @(posedge CLK) disable iff (!CLK) (gray_code_output == {binary_input[3], binary_input[3] ^ binary_input[2], binary_input[2] ^ binary_input[1], binary_input[1] ^ binary_input[0]})
    );

    // Ensure that the barrel shifter shifts the Gray code correctly
    barrel_shifter_behavior: assert property (
        @(posedge CLK) disable iff (!CLK) 
        (shifted_gray_code_output == (shift_amount == 2'b00) ? gray_code_output :
                                  (shift_amount == 2'b01) ? {gray_code_output[2:0], gray_code_output[3]} :
                                  (shift_amount == 2'b10) ? {gray_code_output[1:0], gray_code_output[3:2]} :
                                  {gray_code_output[0], gray_code_output[3:1]})
    );

    // Ensure that the shifted output is within the valid range
    shifted_output_range: assert property (
        @(posedge CLK) disable iff (!CLK) (shifted_gray_code_output[3:0] inside {[0:15]})
    );

endmodule