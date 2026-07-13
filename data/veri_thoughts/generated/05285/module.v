
module mux_transmission_gate (
    input A,
    input B,
    input SEL,
    output reg OUT
);

always @(*) begin
    if (SEL == 1'b0) begin
        OUT = A;
    end else begin
        OUT = B;
    end
end

endmodule