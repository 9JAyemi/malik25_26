
module rotator (
    input clk,
    input load,
    input [1:0] ena,
    input [99:0] data,
    output [99:0] q
);

reg [99:0] shift_reg;
reg [99:0] shifted_out;
reg [1:0] rotate_mode;

always @(posedge clk) begin
    if (load) begin
        shift_reg <= data;
    end else if (ena[0] == 1) begin
        // Rotate right by one bit
        shift_reg <= {shift_reg[0], shift_reg[99:1]};
    end else if (ena[1] == 1) begin
        // Rotate left by one bit
        shift_reg <= {shift_reg[98:0], shift_reg[99]};
    end else if (ena == 2'b11) begin
        // Rotate right by two bits
        shift_reg <= {shift_reg[0], shift_reg[99:2]};
    end
end

assign q = shift_reg;

endmodule
module top_module(
    input clk,
    input load,
    input [1:0] ena,
    input [99:0] data,
    output [99:0] q
);

rotator rotator_inst (
    .clk(clk),
    .load(load),
    .ena(ena),
    .data(data),
    .q(q)
);

endmodule