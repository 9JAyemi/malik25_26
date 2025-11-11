
module top_module (
    input clk,
    input reset, // Synchronous active-high reset
    input [3:0] in1, // 4-bit input for the first port of the multiplexer
    input [3:0] in2, // 4-bit input for the second port of the multiplexer
    input select, // Select input to choose between the inputs of the multiplexer
    input [3:0] add1, // 4-bit input for the first port of the adder
    input [3:0] add2, // 4-bit input for the second port of the adder
    output [3:0] mux_out, // 4-bit output from the selected input of the multiplexer
    output [3:0] add_out, // 4-bit output from the sum of the inputs of the adder
    output [3:0] final_out // 4-bit output from the bitwise XOR operation of the multiplexer and adder outputs
);

wire [3:0] mux_sel;
wire [3:0] add_sum;

mux2to1 mux_inst (
    .in1(in1),
    .in2(in2),
    .select(select),
    .out(mux_sel)
);

adder4bit add_inst (
    .in1(add1),
    .in2(add2),
    .out(add_sum)
);

// Corrected code
reg [3:0] mux_out;
reg [3:0] add_out;
reg [3:0] final_out;

always @(posedge clk) begin
    if (reset) begin
        mux_out <= 4'b0;
        add_out <= 4'b0;
        final_out <= 4'b0;
    end else begin
        mux_out <= mux_sel;
        add_out <= add_sum;
        final_out <= mux_sel ^ add_sum;
    end
end

endmodule
module mux2to1 (
    input [3:0] in1,
    input [3:0] in2,
    input select,
    output [3:0] out
);

assign out = (select == 1) ? in2 : in1;

endmodule
module adder4bit (
    input [3:0] in1,
    input [3:0] in2,
    output [3:0] out
);

assign out = in1 + in2;

endmodule