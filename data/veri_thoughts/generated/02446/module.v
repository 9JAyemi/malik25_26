module top_module (
    input clk,
    input reset,          // Synchronous active-high reset
    output [3:0] q
);

reg [3:0] counter;
wire [3:0] mux2_input1, mux2_input2;
wire [3:0] mux4_input1, mux4_input2, mux4_input3, mux4_input4;

assign mux2_input1 = counter;
assign mux2_input2 = 4'b1111;
assign mux4_input1 = counter;
assign mux4_input2 = 4'b0001;
assign mux4_input3 = 4'b0011;
assign mux4_input4 = 4'b0111;

wire [1:0] mux4_select;
wire mux2_select;

// Binary counter with synchronous active-high reset
always @(posedge clk) begin
    if (reset) begin
        counter <= 4'b0000;
    end else begin
        counter <= counter + 1;
    end
end

// Multiplexer select inputs based on counter output
assign mux4_select = counter[1:0];
assign mux2_select = counter[3];

// 2-to-1 multiplexer
wire [3:0] mux2_output;
mux2 mux2_inst (
    .a(mux2_input1),
    .b(mux2_input2),
    .sel(mux2_select),
    .y(mux2_output)
);

// 4:1 multiplexer
mux4 mux4_inst (
    .a(mux4_input1),
    .b(mux4_input2),
    .c(mux4_input3),
    .d(mux4_input4),
    .sel(mux4_select),
    .y(q)
);

endmodule

// 2-to-1 multiplexer
module mux2 (
    input [3:0] a,
    input [3:0] b,
    input sel,
    output reg [3:0] y
);
always @* begin
    if (sel) begin
        y = b;
    end else begin
        y = a;
    end
end
endmodule

// 4:1 multiplexer
module mux4 (
    input [3:0] a,
    input [3:0] b,
    input [3:0] c,
    input [3:0] d,
    input [1:0] sel,
    output reg [3:0] y
);
always @* begin
    case (sel)
        2'b00: y = a;
        2'b01: y = b;
        2'b10: y = c;
        2'b11: y = d;
    endcase
end
endmodule