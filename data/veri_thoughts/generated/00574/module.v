module comparator(
    input [3:0] A,
    input [3:0] B,
    output reg [1:0] C
);

// Comparing A and B
always @(*) begin
    if(A == B) begin
        C = 2'b00;
    end
    else if(A > B) begin
        C = 2'b01;
    end
    else begin
        C = 2'b10;
    end
end

endmodule