module mux4to1_using_2to1 (
    input [3:0] in0,
    input [3:0] in1,
    input [3:0] in2,
    input [3:0] in3,
    input [1:0] sel,
    output reg [3:0] out
);

wire [3:0] mux1_out;
wire [3:0] mux2_out;

// First 2-to-1 MUX
mux2to1 mux1 (
    .in0(in0),
    .in1(in1),
    .sel(sel[0]),
    .out(mux1_out)
);

// Second 2-to-1 MUX
mux2to1 mux2 (
    .in0(in2),
    .in1(in3),
    .sel(sel[0]),
    .out(mux2_out)
);

// Final 2-to-1 MUX
mux2to1 mux3 (
    .in0(mux1_out),
    .in1(mux2_out),
    .sel(sel[1]),
    .out(out)
);

endmodule

// 2-to-1 MUX module
module mux2to1 (
    input [3:0] in0,
    input [3:0] in1,
    input sel,
    output reg [3:0] out
);

always @(*) begin
    if(sel == 1'b0) begin
        out = in0;
    end
    else begin
        out = in1;
    end
end

endmodule