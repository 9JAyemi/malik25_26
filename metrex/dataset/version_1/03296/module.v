
module pipelined_mux(
    input [7:0] in,
    input [1:0] sel,
    output reg [3:0] out
);

reg [3:0] stage1_out;
reg [3:0] stage2_out;

// Stage 1
always @(*) begin
    case (sel[0])
        1'b0: stage1_out = in[1:0];
        1'b1: stage1_out = in[3:2];
        default: stage1_out = in[5:4];
    endcase
end

// Stage 2
always @(*) begin
    case (sel[1])
        1'b0: stage2_out = stage1_out[1:0];
        1'b1: stage2_out = stage1_out[3:2];
        default: stage2_out = stage1_out[3:2];
    endcase
end

// Output
always @(*) begin
    out = stage2_out;
end

endmodule

module mux2to1(
    input a,
    input b,
    input sel,
    output reg out
);

always @(*) begin
    out = sel ? b : a;
end

endmodule
