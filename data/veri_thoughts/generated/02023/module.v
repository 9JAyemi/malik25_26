module priority_encoder (
    input [7:0] a, b, c, d,
    output [1:0] largest_index);

    wire [7:0] max1, max2, max3;

    assign max1 = (a > b) ? a : b;
    assign max2 = (c > d) ? c : d;
    assign max3 = (max1 > max2) ? max1 : max2;

    assign largest_index = (max3 == a) ? 2'b00 :
                           (max3 == b) ? 2'b01 :
                           (max3 == c) ? 2'b10 :
                                         2'b11;

endmodule

module final_module (
    input [7:0] largest_value, sum,
    output [7:0] final_output);

    assign final_output = sum - largest_value;

endmodule

module top_module (
    input [7:0] a, b, c, d,
    output [7:0] final_output);

    wire [1:0] largest_index;
    wire [7:0] largest_value, sum;

    priority_encoder pe(a, b, c, d, largest_index);
    assign largest_value = (largest_index == 2'b00) ? a :
                           (largest_index == 2'b01) ? b :
                           (largest_index == 2'b10) ? c :
                                                     d;

    assign sum = a + b + c + d;

    final_module fm(largest_value, sum, final_output);

endmodule