module transition_detector (
    input clk,
    input reset,
    input [31:0] in,
    output reg out
);

reg [31:0] in_reg;
reg [31:0] in_reg_prev;
reg [31:0] in_xor;

always @(posedge clk, posedge reset) begin
    if (reset) begin
        in_reg <= 0;
        in_reg_prev <= 0;
        in_xor <= 0;
        out <= 0;
    end else begin
        in_reg <= in;
        in_reg_prev <= in_reg;
        in_xor <= in_reg ^ in_reg_prev;
        if (in_xor != 0) begin
            out <= 1;
        end
    end
end

endmodule

module bitwise_operations (
    input [2:0] a,
    input [2:0] b,
    output [2:0] out_and,
    output [2:0] out_xor,
    output [2:0] out_nor,
    output reg [2:0] a_not,
    output reg [2:0] b_not
);

assign out_and = a & b;
assign out_xor = a ^ b;
assign out_nor = ~(a | b);

always @* begin
    a_not = ~a;
    b_not = ~b;
end

endmodule

module functional_module (
    input clk,
    input reset,
    input transition_detect,
    input [2:0] bitwise_and,
    output reg [2:0] out_and
);

always @(posedge clk, posedge reset) begin
    if (reset) begin
        out_and <= 0;
    end else begin
        if (transition_detect == 1) begin
            out_and <= bitwise_and;
        end
    end
end

endmodule

module top_module (
    input clk,
    input reset,
    input [31:0] in,
    input [2:0] a,
    input [2:0] b,
    output [2:0] out_and_bitwise,
    output [5:0] out_not
);

wire transition_detect;
wire [2:0] bitwise_and;
wire [2:0] bitwise_xor;
wire [2:0] bitwise_nor;
wire [2:0] a_not;
wire [2:0] b_not;

transition_detector td(clk, reset, in, transition_detect);
bitwise_operations bo(a, b, bitwise_and, bitwise_xor, bitwise_nor, a_not, b_not);
functional_module fm(clk, reset, transition_detect, bitwise_and, out_and_bitwise);

assign out_not = {b_not, a_not};

endmodule