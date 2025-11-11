
module adder_subtractor (
    input [31:0] a,
    input [31:0] b,
    input sub,
    output reg [31:0] sum,
    output reg [31:0] sum_reverse
);
    always @(*) begin
        sum = sub ? a - b : a + b;
        sum_reverse = {sum[31:24], sum[23:16], sum[15:8], sum[7:0]};
    end
endmodule
module byte_reversal (
    input [31:0] input_data,
    output reg [31:0] output_data
);
    always @(*) begin
        output_data = {input_data[31:24], input_data[23:16], input_data[15:8], input_data[7:0]};
    end
endmodule
module functional_module (
    input [31:0] input1,
    input [31:0] input2,
    output reg [31:0] final_output
);
    always @(*) begin
        final_output = input1 + input2;
    end
endmodule
module top_module (
    input [31:0] a,
    input [31:0] b,
    input sub,
    output [31:0] sum,
    output [31:0] sum_reverse,
    output [31:0] final_output
);
    wire [31:0] add_sub_result;
    wire [31:0] byte_reversal_result;
    adder_subtractor add_sub_module (
        .a(a),
        .b(b),
        .sub(sub),
        .sum(add_sub_result)
    );
    byte_reversal byte_reversal_module (
        .input_data(add_sub_result),
        .output_data(byte_reversal_result)
    );
    functional_module functional_module (
        .input1(byte_reversal_result),
        .input2(add_sub_result),
        .final_output(final_output)
    );
    assign sum = add_sub_result;
    assign sum_reverse = byte_reversal_result;
endmodule