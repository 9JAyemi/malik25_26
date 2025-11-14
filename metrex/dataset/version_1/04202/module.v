module top_module (
    input clk,
    input reset,
    input [7:0] data_in,
    input select,
    output reg [7:0] final_output
);

wire [1:0] out2;
wire [1:0] out1;
wire [1:0] out0;
wire [1:0] mux_out; 

split_input split_input_inst (
    .in_vec(data_in),
    .out2(out2),
    .out1(out1),
    .out0(out0)
);

mux mux_inst (
    .a(out0),
    .b(out1),
    .c(out2),
    .s(select),
    .out(mux_out)
);

always @(posedge clk) begin
    if (reset) begin
        final_output <= 8'b00000000;
    end else begin
        final_output <= {6'b000000, mux_out}; 
    end
end

endmodule


module split_input (
    input wire [7:0] in_vec,
    output reg [1:0] out2,
    output reg [1:0] out1,
    output reg [1:0] out0
);

always @(*) begin
    out2 = in_vec[7:6];
    out1 = in_vec[5:4];
    out0 = in_vec[3:2];
end

endmodule

module mux (
    input [1:0] a, b, c,
    input s,
    output reg [1:0] out 
);

always @(*) begin
    case (s)
        1'b0: out = a;
        1'b1: out = b;
        default: out = 2'b00; 
    endcase
end

endmodule
