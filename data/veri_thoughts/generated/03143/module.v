
module max_finder (
    input [15:0] D,
    output reg [15:0] max
);

reg [15:0] shifted_D;
reg [3:0] highest_bit;

always @ (D) begin
    highest_bit = D >> 12;
    shifted_D = D >> highest_bit;
    max = shifted_D;
end

endmodule