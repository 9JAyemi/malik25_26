
module barrel_shifter (
    input [7:0] in,
    output [7:0] out
);
    assign out = {in[7], in[6], in[5], in[4], in[3], in[2], in[1], in[0]};
endmodule
module rising_edge_detector (
    input clk,
    input [31:0] in32,
    input reset,
    output reg [31:0] out
);
    reg [31:0] prev_in;
    reg [31:0] rising_edge_mask;
    
    always @(posedge clk or posedge reset) begin
        if (reset) begin
            prev_in <= 32'b0;
            rising_edge_mask <= 32'b0;
            out <= 32'b0;
        end else begin
            prev_in <= in32;
            rising_edge_mask <= (in32 ^ prev_in) & in32;
            out <= out | rising_edge_mask;
        end
    end
endmodule
module bitwise_or (
    input [31:0] in1,
    input [31:0] in2,
    output [31:0] out
);
    assign out = in1 | in2;
endmodule
module top_module (
    input clk,
    input reset,
    input [7:0] in,
    input [31:0] in32,
    output reg [31:0] out
);
    wire [7:0] reversed_in;
    wire [31:0] rising_edge_out;
    
    barrel_shifter bs (
        .in(in),
        .out(reversed_in)
    );
    
    rising_edge_detector red (
        .clk(clk),
        .in32(in32),
        .reset(reset),
        .out(rising_edge_out)
    );
    
    bitwise_or bo (
        .in1({24'b0, reversed_in}),
        .in2(rising_edge_out),
        .out(out)
    );
endmodule