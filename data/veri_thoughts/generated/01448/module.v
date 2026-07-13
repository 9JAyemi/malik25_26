
module dff_or (
    input clk,
    input reset,
    input [7:0] d,
    input [7:0] e,
    output wire [7:0] q
);

reg [7:0] q_reg;

always @(posedge clk or posedge reset) begin
    if (reset) begin
        q_reg <= {8'b00000001, 8'b00000010, 8'b00000100, 8'b00001000, 8'b00010000, 8'b00100000, 8'b01000000, 8'b10000000};
    end else begin
        q_reg <= d;
    end
end

assign q = q_reg | e;

endmodule