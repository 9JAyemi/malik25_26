
module comparator (
    input [3:0] a,
    input [3:0] b,
    output reg out
);

    always @(*) begin
        if (a == b) begin
            out = 1'bX;
        end
        else if (a > b) begin
            out = 1'b1;
        end
        else begin
            out = 1'b0;
        end
    end

endmodule