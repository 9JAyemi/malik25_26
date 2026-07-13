
module U2 (
    input [7:0] A,
    input [7:0] B,
    output [7:0] OUT
);

    reg [7:0] out_reg;

    always @(*) begin
        out_reg = (A >= B) ? (A - B) : (B - A);
    end

    assign OUT = out_reg;

endmodule
