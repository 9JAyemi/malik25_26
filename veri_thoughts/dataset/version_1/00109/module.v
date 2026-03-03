module absolute_value (
    input signed [31:0] in,
    output reg signed [31:0] out
);

    always @(*) begin
        if (in < 0) begin
            out = -in;
        end else begin
            out = in;
        end
    end

endmodule