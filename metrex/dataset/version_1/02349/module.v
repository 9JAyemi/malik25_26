module top_module (
    input [7:0] a,
    input [7:0] b,
    output reg [7:0] final_result
);

    // Multiplication module
    wire [15:0] mult_result;
    wire mult_sign;
    multiplier_module mult_inst (
        .a(a),
        .b(b),
        .result(mult_result),
        .sign(mult_sign)
    );
    
    // Ripple carry adder module
    wire [3:0] adder_result;
    ripple_carry_adder adder_inst (
        .a(a[3:0]),
        .b(b[3:0]),
        .carry_in(1'b0),
        .sum(adder_result)
    );
    
    // Additional functional module
    wire [4:0] sum_abs;
    absolute_value_module abs_inst (
        .input_sum({mult_result[15], adder_result}),
        .output_abs(sum_abs)
    );
    
    // Output final result
    always @(*) begin
        if (mult_sign) begin
            final_result = -{sum_abs, 4'b0};
        end else begin
            final_result = {sum_abs, 4'b0};
        end
    end

endmodule


module multiplier_module (
    input [7:0] a,
    input [7:0] b,
    output reg [15:0] result,
    output reg sign
);

    always @(*) begin
        if ((a[7] == 1) && (b[7] == 1)) begin
            result = ~(a*b) + 1;
            sign = 1;
        end else if ((a[7] == 0) && (b[7] == 0)) begin
            result = a*b;
            sign = 0;
        end else begin
            result = a*b;
            sign = 1;
        end
    end

endmodule


module ripple_carry_adder (
    input [3:0] a,
    input [3:0] b,
    input carry_in,
    output reg [3:0] sum
);

    reg carry_out;
    
    always @(*) begin
        sum = a + b + carry_in;
        carry_out = (sum > 4'b1111);
        sum = sum & 4'b1111;
    end

endmodule


module absolute_value_module (
    input [4:0] input_sum,
    output reg [4:0] output_abs
);

    always @(*) begin
        if (input_sum[4] == 1) begin
            output_abs = ~input_sum + 1;
        end else begin
            output_abs = input_sum;
        end
    end

endmodule