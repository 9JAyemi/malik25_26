module calc(
    input [3:0] num1,
    input [3:0] num2,
    input op,
    output reg [3:0] result
);

    always @(*) begin
        if(op == 0) begin // addition
            result <= num1 + num2;
        end else begin // subtraction
            result <= num1 - num2;
        end
    end

endmodule