
module mux_2_1 (
    input A,
    input B,
    input SEL,
    output reg OUT
);

always @(*) begin
    if (SEL == 1'b0)
        OUT = A;
    else
        OUT = B;
end

endmodule