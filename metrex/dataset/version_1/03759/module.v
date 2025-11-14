
module dff_mux (
    input clk,
    input [7:0] d,
    input [2:0] sel,
    output reg [7:0] q
);

reg [7:0] q_int;
reg [7:0] d_int;

always @(posedge clk) begin
    q_int <= d_int;
    d_int <= d;
end

always @(*) begin
    case (sel)
        3'b000: q = q_int[7];
        3'b001: q = q_int[6];
        3'b010: q = q_int[5];
        3'b011: q = q_int[4];
        3'b100: q = q_int[3];
        3'b101: q = q_int[2];
        3'b110: q = q_int[1];
        3'b111: q = q_int[0];
    endcase
end

endmodule
module top_module (
    input clk,
    input [7:0] d,
    output [7:0] q
);

wire [2:0] sel;
reg [7:0] d_int;

dff_mux mux_inst (
    .clk(clk),
    .d(d_int),
    .sel(sel),
    .q(q)
);

assign sel[2:0] = d[2:0]; 

always @(posedge clk) begin
    d_int <= d;
end

endmodule