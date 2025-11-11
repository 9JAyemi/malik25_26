
module unsigned_multiplier (
    input [7:0] a,
    input [7:0] b,
    output reg [15:0] p
);

reg [7:0] shift_reg;
reg [3:0] count;

always @(a, b) begin
    p = 0;
    shift_reg = b;
    count = 8;

    for (count = 8; count > 0; count = count - 1) begin
        if (shift_reg[0] == 1) begin
            p = p + (a << (8 - count));
        end
        shift_reg = shift_reg >> 1;
    end
end

endmodule