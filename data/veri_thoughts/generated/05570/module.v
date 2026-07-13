module mux_6to1 (
    input [2:0] sel,
    input [3:0] data0,
    input [3:0] data1,
    input [3:0] data2,
    input [3:0] data3,
    input [3:0] data4,
    input [3:0] data5,
    output reg [3:0] out
);

always @(*) begin
    case (sel)
        3'b000: out = data0;
        3'b001: out = data1;
        3'b010: out = data2;
        3'b011: out = data3;
        3'b100: out = data4;
        3'b101: out = data5;
        default: out = 4'b0000;
    endcase
end

endmodule

module dff_8 (
    input clk,
    input reset,
    input [7:0] d,
    output reg [7:0] q
);

always @(posedge clk, negedge reset) begin
    if (reset == 1'b0) begin
        q <= 8'b00000000;
    end else begin
        q <= d;
    end
end

endmodule

module functional_module (
    input clk,
    input reset,
    input [2:0] sel,
    input [3:0] data0,
    input [3:0] data1,
    input [3:0] data2,
    input [3:0] data3,
    input [3:0] data4,
    input [3:0] data5,
    input [7:0] d,
    input select,
    output [7:0] q
);

wire [3:0] mux_out;
mux_6to1 mux_inst (
    .sel(sel),
    .data0(data0),
    .data1(data1),
    .data2(data2),
    .data3(data3),
    .data4(data4),
    .data5(data5),
    .out(mux_out)
);

reg [7:0] d_reg;
always @(posedge clk, negedge reset) begin
    if (reset == 1'b0) begin
        d_reg <= 8'b00000000;
    end else if (select == 1'b1) begin
        d_reg <= {d_reg[6:0], mux_out};
    end
end

dff_8 dff_inst (
    .clk(clk),
    .reset(reset),
    .d(d_reg),
    .q(q)
);

endmodule

module top_module (
    input clk,
    input reset,
    input [2:0] sel,
    input [3:0] data0,
    input [3:0] data1,
    input [3:0] data2,
    input [3:0] data3,
    input [3:0] data4,
    input [3:0] data5,
    input [7:0] d,
    input select,
    output [7:0] q
);

functional_module func_inst (
    .clk(clk),
    .reset(reset),
    .sel(sel),
    .data0(data0),
    .data1(data1),
    .data2(data2),
    .data3(data3),
    .data4(data4),
    .data5(data5),
    .d(d),
    .select(select),
    .q(q)
);

endmodule