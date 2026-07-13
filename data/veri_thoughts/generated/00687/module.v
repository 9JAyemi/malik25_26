module top_module (
    input a,
    input b,
    input sel_b1,
    input sel_b2,
    input clk,
    input [2:0] sel, 
    input [3:0] data0,
    input [3:0] data1,
    input [3:0] data2,
    input [3:0] data3,
    input [3:0] data4,
    input [3:0] data5,
    output reg [7:0] sum_out
);

reg out_2to1_mux;
wire [3:0] out_6to1_mux;

always @(posedge clk) begin
    if (sel_b1 && sel_b2)
        out_2to1_mux <= b;
    else
        out_2to1_mux <= a;
end

mux_6to1 mux_inst (
    .sel(sel),
    .data0(data0),
    .data1(data1),
    .data2(data2),
    .data3(data3),
    .data4(data4),
    .data5(data5),
    .out(out_6to1_mux)
);

always @(posedge clk) begin
    sum_out <= out_2to1_mux + out_6to1_mux;
end

endmodule

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
        default: out = data0;
    endcase
end

endmodule