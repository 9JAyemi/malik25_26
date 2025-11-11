
module top_module (
    input clk,
    input reset,
    input [7:0] a,
    input [7:0] b,
    input select,
    output reg [7:0] sum,
    output reg [7:0] min,
    output [15:0] product
);

    wire [7:0] min_value;
    wire [7:0] adder_sum;
    
    find_min min_module(
        .a(a),
        .b(b),
        .c(8'h0),
        .d(8'h0),
        .min(min_value)
    );
    
    adder adder_module(
        .a(a),
        .b(b),
        .sum(adder_sum)
    );
    
    always @(posedge clk) begin
        if (reset) begin
            sum <= 8'h0;
            min <= 8'h0;
        end else begin
            if (select) begin
                sum <= adder_sum;
                min <= min_value;
            end else begin
                sum <= min_value;
                min <= adder_sum;
            end
        end
    end
    
    assign product = {adder_sum, min_value};
    
endmodule

module find_min (
    input [7:0] a,
    input [7:0] b,
    input [7:0] c,
    input [7:0] d,
    output [7:0] min
);
    wire [7:0] ab_min;
    wire [7:0] cd_min;
    
    assign ab_min = (a < b) ? a : b;
    assign cd_min = (c < d) ? c : d;
    
    assign min = (ab_min < cd_min) ? ab_min : cd_min;
    
endmodule

module adder (
    input [7:0] a,
    input [7:0] b,
    output [7:0] sum
);
    assign sum = a + b;
endmodule
