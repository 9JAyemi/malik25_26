module edge_detector(
    input clk,
    input [7:0] in,
    output reg [7:0] out
);
    reg [7:0] prev_in;
    always @(posedge clk) begin
        if (in > prev_in) begin
            out <= in;
        end else if (in < prev_in) begin
            out <= in;
        end
        prev_in <= in;
    end
endmodule

module mux(
    input [7:0] in1,
    input [7:0] in2,
    input [7:0] in3,
    input [7:0] in4,
    input sel_b1,
    input sel_b2,
    output reg [7:0] out
);
    always @(*) begin
        if (sel_b1 == 0 && sel_b2 == 0) begin
            out = in1;
        end else if (sel_b1 == 0 && sel_b2 == 1) begin
            out = in2;
        end else if (sel_b1 == 1 && sel_b2 == 0) begin
            out = in3;
        end else if (sel_b1 == 1 && sel_b2 == 1) begin
            out = in4;
        end
    end
endmodule

module top_module(
    input clk,
    input [7:0] in,
    input [7:0] input1,
    input [7:0] input2,
    input [7:0] input3,
    input [7:0] input4,
    input sel_b1,
    input sel_b2,
    output [7:0] out
);
    wire [7:0] edge_detect_out;
    edge_detector edge_detect(.clk(clk), .in(in), .out(edge_detect_out));
    
    wire [7:0] mux_out;
    mux mux_inst(.in1(input1), .in2(input2), .in3(input3), .in4(input4), .sel_b1(sel_b1), .sel_b2(sel_b2), .out(mux_out));
    
    assign out = edge_detect_out & mux_out;
endmodule