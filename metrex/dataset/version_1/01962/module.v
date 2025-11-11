module shift_reg (
    input clk,
    input [7:0] d,
    output reg [7:0] q
);

always @(posedge clk) begin
    q <= {q[6:0], d};
end

endmodule

module d_ff (
    input clk,
    input d,
    output reg q
);

always @(negedge clk) begin
    q <= d;
end

endmodule

module concat_module (
    input [7:0] shift_reg_out,
    input [0:0] d_ff_out,
    output [15:0] q
);

assign q = {shift_reg_out, d_ff_out};

endmodule

module top_module (
    input clk,
    input [7:0] d,
    output [15:0] q
);

wire [7:0] shift_reg_out;
wire [0:0] d_ff_out;

shift_reg shift_reg_inst (
    .clk(clk),
    .d(d),
    .q(shift_reg_out)
);

d_ff d_ff_inst (
    .clk(clk),
    .d(shift_reg_out[7]),
    .q(d_ff_out)
);

concat_module concat_inst (
    .shift_reg_out(shift_reg_out),
    .d_ff_out(d_ff_out),
    .q(q)
);

endmodule