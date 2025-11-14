module adder_32bit (
    input [31:0] a,
    input [31:0] b,
    output [31:0] sum
);
    wire [31:0] carry;
    wire [31:0] temp_sum;
    wire [31:0] temp_carry;
    
    assign temp_carry[0] = a[0] & b[0];
    assign temp_sum[0] = a[0] ^ b[0];
    
    generate
        genvar i;
        for (i = 1; i < 32; i = i + 1) begin : generate_loop
            assign temp_carry[i] = (a[i] & b[i]) | (a[i] & temp_sum[i-1]) | (b[i] & temp_sum[i-1]);
            assign temp_sum[i] = a[i] ^ b[i] ^ temp_sum[i-1];
        end
    endgenerate
    
    assign carry = temp_carry[31];
    assign sum = {temp_sum[31], temp_sum[30:0]} + (carry ? 1 : 0);
    
endmodule
module bitwise_logic_3bit (
    input [2:0] a,
    input [2:0] b,
    output [2:0] out_or,
    output out_logical_or,
    output [5:0] out_not
);
    assign out_or = a | b;
    assign out_logical_or = (a != 3'b000) || (b != 3'b000);
    assign out_not = {~b, ~a};
endmodule
module top_module (
    input [31:0] a,
    input [31:0] b,
    input [2:0] in_bitwise_a,
    input [2:0] in_bitwise_b,
    output [31:0] final_output,
    output [2:0] out_or_bitwise,
    output out_or_logical,
    output [5:0] out_not
);
    wire [31:0] adder_output;
    wire [2:0] bitwise_output_or;
    wire bitwise_output_logical_or;
    wire [5:0] bitwise_output_not;
    
    adder_32bit adder_inst (
        .a(a),
        .b(b),
        .sum(adder_output)
    );
    
    bitwise_logic_3bit bitwise_inst (
        .a(in_bitwise_a),
        .b(in_bitwise_b),
        .out_or(bitwise_output_or),
        .out_logical_or(bitwise_output_logical_or),
        .out_not(bitwise_output_not)
    );
    
    assign final_output = adder_output + {bitwise_output_not[5:3], bitwise_output_not[2:0], bitwise_output_not[5:3], bitwise_output_not[2:0]} + {bitwise_output_or[2], bitwise_output_or[1], bitwise_output_or[0], 3'b000};
    assign out_or_bitwise = bitwise_output_or;
    assign out_or_logical = bitwise_output_logical_or;
    assign out_not = bitwise_output_not;
    
endmodule
