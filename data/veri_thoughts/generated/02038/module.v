module binary_adder_4bit(
    input [3:0] A, 
    input [3:0] B, 
    input CI, 
    input CLK, 
    output reg [3:0] SUM, 
    output CO
);

reg [4:0] C;

always @(posedge CLK) begin
    SUM <= A + B + C[3:0];
    C <= (A + B + C) > 4'b1111 ? 1 : 0;
end

assign CO = C[4];

endmodule