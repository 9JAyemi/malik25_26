module priority_encoder_mux (
    input [7:0] in,
    input a,
    input b,
    input clk,
    output reg out_always,
    output reg [2:0] pos
);

reg [7:0] in_reg;
reg [2:0] pos_reg;
wire [2:0] pos_wire;
wire sel;

priority_encoder pe(
    .in(in_reg),
    .out(pos_wire)
);

assign sel = (pos_wire != 3'b0);

always @(posedge clk) begin
    if (sel) begin
        out_always <= b;
    end else begin
        out_always <= a;
    end
end

always @(posedge clk) begin
    if (sel) begin
        pos_reg <= pos_wire;
    end else begin
        pos_reg <= 3'b0;
    end
end

always @(posedge clk) begin
    in_reg <= in;
end

always @* begin
    pos = pos_reg;
end

endmodule

module priority_encoder (
    input [7:0] in,
    output reg [2:0] out
);

always @* begin
    casez(in)
        8'b1xxxxxxx: out = 2;
        8'b01xxxxxx: out = 1;
        8'b001xxxxx: out = 0;
        default: out = 3'b0;
    endcase
end

endmodule