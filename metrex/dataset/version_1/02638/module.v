module comparator (
    input [15:0] A,
    input [15:0] B,
    output reg out
);

    always @(*) begin
        if (A > B) begin
            out = 1'b1;
        end else if (A < B) begin
            out = 1'b0;
        end else begin
            out = 1'b0;
        end
    end

endmodule