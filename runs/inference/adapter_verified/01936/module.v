
module xor_shift_register (
    input clk,
    input load,
    input [1:0] ena,
    input [99:0] data,
    output [99:0] q,
    output out_if_else
);

reg [99:0] shift_reg;

always @(posedge clk) begin
    if (load) begin
        shift_reg <= data;
    end else begin // Fixed the if-else condition here
        if (ena != 2'b00) begin
            shift_reg <= {shift_reg[98-2'd1 : 0], shift_reg[99 : 98+2'd0]};
        end
    end
end

assign out_if_else = (shift_reg ^ data) ? 1'b1 : 1'b0;
assign q = shift_reg;

endmodule
