module multiplier (
    input [3:0] A,
    input [3:0] B,
    output reg [7:0] OUT
);

reg [7:0] result;
reg [3:0] temp_A;
reg [3:0] temp_B;

integer i;

always @(*) begin
    result = 8'b0;
    temp_A = A;
    temp_B = B;

    for (i = 0; i < 4; i = i + 1) begin
        if (temp_B[0]) begin
            result = result + (temp_A << i);
        end
        temp_B = temp_B >> 1;
    end

    OUT <= result;
end

endmodule