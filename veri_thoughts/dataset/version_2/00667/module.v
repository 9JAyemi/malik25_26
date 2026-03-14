module add_two_signals (
    input [3:0] A,
    input [3:0] B,
    output reg [3:0] sum,
    output reg carry_out
);

reg [4:0] sum_temp; 

always @(*) begin
    sum_temp = A + B;
    carry_out = (sum_temp[4] == 1);
    sum = sum_temp[3:0];
end

endmodule