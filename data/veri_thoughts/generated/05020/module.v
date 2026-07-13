
module mux4to1 (
    input [7:0] a,
    input [7:0] b,
    input [7:0] c,
    input [7:0] d,
    input [1:0] s,
    output reg [7:0] w
);

always @(a or b or c or d or s) begin
    case (s)
        2'b00: w = a;
        2'b01: w = b;
        2'b10: w = c;
        2'b11: w = d;
    endcase
end

endmodule
