module top_module (
    input clk,
    input reset,
    input [7:0] a,
    input [7:0] b,
    output [7:0] sum_output,
    output [7:0] product_output,
    output [7:0] difference_output
);

// Instantiate the adder module
adder_module adder_inst(
    .clk(clk),
    .reset(reset),
    .a(a),
    .b(b),
    .sum(sum_output)
);

// Instantiate the multiplier module
multiplier_module multiplier_inst(
    .clk(clk),
    .reset(reset),
    .a(a),
    .b(b),
    .product(product_output)
);

// Instantiate the difference module
difference_module difference_inst(
    .clk(clk),
    .reset(reset),
    .a(sum_output),
    .b(product_output),
    .difference(difference_output)
);

endmodule

// 8-bit binary adder module
module adder_module (
    input clk,
    input reset,
    input [7:0] a,
    input [7:0] b,
    output reg [7:0] sum
);

always @(posedge clk) begin
    if (reset) begin
        sum <= 0;
    end else begin
        sum <= a + b;
    end
end

endmodule

// 8-bit binary multiplier module
module multiplier_module (
    input clk,
    input reset,
    input [7:0] a,
    input [7:0] b,
    output reg [7:0] product
);

always @(posedge clk) begin
    if (reset) begin
        product <= 0;
    end else begin
        product <= a * b;
    end
end

endmodule

// Difference module
module difference_module (
    input clk,
    input reset,
    input [7:0] a,
    input [7:0] b,
    output reg [7:0] difference
);

always @(posedge clk) begin
    if (reset) begin
        difference <= 0;
    end else begin
        difference <= a - b;
    end
end

endmodule