module mux_4to1 (
    input A,
    input B,
    input C,
    input D,
    input [1:0] SEL,
    output reg Y
);

    always @(*) begin
        case (SEL)
            2'b00: Y = A;
            2'b01: Y = B;
            2'b10: Y = C;
            2'b11: Y = D;
        endcase;
    end

endmodule