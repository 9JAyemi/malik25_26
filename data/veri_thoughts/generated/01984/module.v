module binary_ones_complement (
    input [3:0] B,
    output reg [3:0] C
);

    always @ (B) begin
        C <= ~B;
    end

endmodule