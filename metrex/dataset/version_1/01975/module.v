
module decoder (
    input [2:0] ABC,
    input clk,  // Clock input added
    output reg [7:0] Y
);

reg [2:0] A, B, C;
reg [7:0] Y_temp;

always @ (posedge clk) begin
    A <= ABC[0];
    B <= ABC[1];
    C <= ABC[2];
end

always @ (posedge clk) begin
    Y_temp <= 8'b00000000;
    if (A == 0 && B == 0 && C == 0) Y_temp[0] <= 1;
    else if (A == 0 && B == 0 && C == 1) Y_temp[1] <= 1;
    else if (A == 0 && B == 1 && C == 0) Y_temp[2] <= 1;
    else if (A == 0 && B == 1 && C == 1) Y_temp[3] <= 1;
    else if (A == 1 && B == 0 && C == 0) Y_temp[4] <= 1;
    else if (A == 1 && B == 0 && C == 1) Y_temp[5] <= 1;
    else if (A == 1 && B == 1 && C == 0) Y_temp[6] <= 1;
    else if (A == 1 && B == 1 && C == 1) Y_temp[7] <= 1;
end

always @ (posedge clk) begin
    Y <= Y_temp;
end

endmodule
