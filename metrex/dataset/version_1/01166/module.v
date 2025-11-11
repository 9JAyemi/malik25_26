
module byte_reversal (
    input [31:0] input_word,
    output [31:0] output_word
);

    assign output_word[7:0] = input_word[31:24];
    assign output_word[15:8] = input_word[23:16];
    assign output_word[23:16] = input_word[15:8];
    assign output_word[31:24] = input_word[7:0];

endmodule
module reg_with_reset (
    input clk,
    input reset,
    input [7:0] input_data,
    output reg [7:0] output_data
);

    always @(posedge clk) begin
        if (reset == 0) begin
            output_data <= 8'h34;
        end else begin
            output_data <= input_data;
        end
    end

endmodule
module bitwise_or (
    input [7:0] input_a,
    input [7:0] input_b,
    output [7:0] output_data
);

    assign output_data = input_a | input_b;

endmodule
module top_module (
    input clk,
    input reset,
    input [7:0] reg_input,
    input [31:0] byte_input,
    output [7:0] func_output
);

    wire [7:0] reg_output;
    wire [31:0] byte_output;

    reg_with_reset reg_inst (
        .clk(clk),
        .reset(reset),
        .input_data(reg_input),
        .output_data(reg_output)
    );

    byte_reversal byte_inst (
        .input_word(byte_input),
        .output_word(byte_output)
    );

    bitwise_or or_inst (
        .input_a(reg_output),
        .input_b(byte_output[31:24]),
        .output_data(func_output)
    );

endmodule