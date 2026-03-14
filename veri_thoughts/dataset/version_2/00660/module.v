
module top_module (
    input clk,
    input reset,
    input data,
    output q
);

wire [2:0] shift_reg_out;
wire d_ff_out;

shift_register shift_reg(
    .clk(clk),
    .reset(reset),
    .data(data),
    .q(shift_reg_out)
);

d_ff d_ff(  // Fixed the spelling
    .clk(clk),
    .reset(reset),
    .d(shift_reg_out[2]),
    .q(d_ff_out)
);

assign q = shift_reg_out[2] ^ d_ff_out;

endmodule

module shift_register(
    input clk,
    input reset,
    input data,
    output reg [2:0] q
);

always @(posedge clk) begin // Changed negative edge to positive edge for posedge
    if (reset) begin
        q <= 3'b0;
    end else begin
        q <= {q[1:0], data};
    end
end

endmodule

module d_ff (
    input clk,
    input reset,
    input d,
    output reg q
);

always @(posedge clk) begin // Changed negative edge to positive edge for posedge
    if (reset) begin
        q <= 1'b0;
    end else begin
        q <= d;
    end
end

endmodule
