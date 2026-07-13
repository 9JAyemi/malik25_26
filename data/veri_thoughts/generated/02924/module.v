module mux4to1(
    input [3:0] A, B, C, D,
    input S0, S1,
    output reg Y
);

always @ (*)
begin
    case ({S1, S0})
        2'b00: Y = A;
        2'b01: Y = B;
        2'b10: Y = C;
        2'b11: Y = D;
        default: Y = 1'bx;
    endcase
end

endmodule