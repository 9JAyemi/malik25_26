module adder_subtractor (
    input [3:0] A,
    input [3:0] B,
    input mode,
    output reg [3:0] result
);

    always @(*) begin
        if (mode == 1'b0) begin
            result = A + B;
        end else begin
            result = A - B;
        end
    end
    
endmodule