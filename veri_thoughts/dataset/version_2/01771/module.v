module comparator_4bit (
    input [3:0] A,
    input [3:0] B,
    output reg [1:0] OUT
);

    always @(*) begin
        if (A > B) begin
            OUT = 2'b01;
        end else if (A < B) begin
            OUT = 2'b10;
        end else begin
            OUT = 2'b11;
        end
    end

endmodule