module mux_2to1 (
    // Inputs
    input A,
    input B,
    input SEL,
    // Outputs
    output reg OUT
);

always @(*) begin
    if (SEL == 1'b1) begin
        OUT = B;
    end else begin
        OUT = A;
    end
end

endmodule