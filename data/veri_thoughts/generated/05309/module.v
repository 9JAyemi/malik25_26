module adder_subtractor (
    input [3:0] a,
    input [3:0] b,
    input control,
    output reg [3:0] out
);

    always @(*) begin
        if (control) begin
            out <= a + b;
        end else begin
            out <= a - b;
        end
    end

endmodule