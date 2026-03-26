module binary_counter (
    input clk,
    input reset,
    output reg [3:0] count
);

always @(posedge clk, posedge reset) begin
    if (reset) begin
        count <= 4'b0000;
    end else begin
        count <= count + 1;
    end
end

endmodule

module mux_2to1 (
    input [3:0] in1,
    input [3:0] in2,
    input select,
    output reg [3:0] out
);

always @(*) begin
    if (select) begin
        out = in2;
    end else begin
        out = in1;
    end
end

endmodule

module adder (
    input [3:0] in1,
    input [3:0] in2,
    output reg [3:0] sum
);

always @(*) begin
    sum = in1 + in2;
end

endmodule

module top_module ( 
    input clk,
    input reset,
    input [3:0] mux_in1,
    input [3:0] mux_in2,
    input select,
    output [3:0] sum
);

wire [3:0] counter_out;
wire [3:0] mux_out;

binary_counter counter (
    .clk(clk),
    .reset(reset),
    .count(counter_out)
);

mux_2to1 mux (
    .in1(mux_in1),
    .in2(mux_in2),
    .select(select),
    .out(mux_out)
);

adder add (
    .in1(counter_out),
    .in2(mux_out),
    .sum(sum)
);

endmodule