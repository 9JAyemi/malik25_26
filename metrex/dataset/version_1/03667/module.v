module top_module (
    input CLK,
    input RST,
    input LD,
    input [3:0] D,
    input [3:0] in,
    input [1:0] sel,
    input enable,
    output [3:0] OUT
);

wire [3:0] mux_out;
wire [3:0] shift_reg_out;

mux_4to1 mux_inst (
    .in(in),
    .sel(sel),
    .enable(enable),
    .out(mux_out)
);

shift_register shift_reg_inst (
    .CLK(CLK),
    .RST(RST),
    .LD(LD),
    .D(D),
    .Q(shift_reg_out)
);

assign OUT = mux_out & shift_reg_out;

endmodule

module mux_4to1 (
    input [3:0] in,
    input [1:0] sel,
    input enable,
    output [3:0] out
);

reg [3:0] out_reg;

always @(*) begin
    if (enable) begin
        case (sel)
            2'b00: out_reg = in[0];
            2'b01: out_reg = in[1];
            2'b10: out_reg = in[2];
            2'b11: out_reg = in[3];
            default: out_reg = 4'b0;
        endcase
    end else begin
        out_reg = 4'b0;
    end
end

assign out = out_reg;

endmodule

module shift_register (
    input CLK,
    input RST,
    input LD,
    input [3:0] D,
    output [3:0] Q
);

reg [3:0] Q_reg;

always @(posedge CLK or posedge RST) begin
    if (RST) begin
        Q_reg <= 4'b0;
    end else begin
        if (LD) begin
            Q_reg <= D;
        end else begin
            Q_reg <= {Q_reg[2:0], Q_reg[3]};
        end
    end
end

assign Q = Q_reg;

endmodule