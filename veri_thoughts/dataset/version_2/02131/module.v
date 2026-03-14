module add_sub (
    input [3:0] a,
    input [3:0] b,
    input sub,
    output reg [3:0] result
);

    always @(*) begin
        if (sub) begin
            result = a - b;
        end else begin
            result = a + b;
        end
    end

endmodule