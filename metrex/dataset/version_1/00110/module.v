
module shift_reg(
    input clk,
    input [2:0] select,
    input [7:0] in,
    output [7:0] out
);

reg [7:0] out_reg;

always @(posedge clk) begin
    case(select)
        3'b000: out_reg <= in;
        3'b001: out_reg <= {in[7], out_reg[6:0]};
        3'b010: out_reg <= {in[7:1], out_reg[0]};
        3'b011: out_reg <= {in, out_reg[7:1]};
        3'b100: out_reg <= {in, out_reg[7:2]};
        3'b101: out_reg <= {in, out_reg[7:3]};
        3'b110: out_reg <= {in, out_reg[7:4]};
        3'b111: out_reg <= {in, out_reg[7:5]};
    endcase
end

assign out = out_reg;

endmodule

module reg_module(
    input clk,
    input reset,
    input [7:0] in,
    output [7:0] out
);

reg [7:0] out_reg;

always @(posedge clk or posedge reset) begin
    if(reset) begin
        out_reg <= 8'b0;
    end else begin
        out_reg <= in;
    end
end

assign out = out_reg;

endmodule

module concat_module(
    input [7:0] a,
    input [7:0] b,
    input [7:0] c,
    input [7:0] d,
    output [31:0] out
);

assign out = {a, b, c, d};

endmodule

module top_module(
    input clk,
    input reset,
    input [31:0] in,
    output [31:0] out
);

wire [7:0] byte1, byte2, byte3, byte4;
wire [7:0] reg_out;

shift_reg shift_reg1(.clk(clk), .select(3'b001), .in(in[23:16]), .out(byte2));
reg_module reg_module1(.clk(clk), .reset(reset), .in(byte2), .out(reg_out));
shift_reg shift_reg2(.clk(clk), .select(3'b010), .in(in[15:8]), .out(byte3));
shift_reg shift_reg3(.clk(clk), .select(3'b111), .in(in[31:24]), .out(byte4));
concat_module concat_module1(.a(byte4), .b(reg_out), .c(byte3), .d(in[7:0]), .out(out));

endmodule
