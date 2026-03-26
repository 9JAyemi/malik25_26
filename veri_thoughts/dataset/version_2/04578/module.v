
module twos_complement (
    input [3:0] in,
    output [3:0] out
);

reg [7:0] sign_extended;
reg [7:0] twos_complement;
reg [3:0] out; // Change from wire to reg

always @(*) begin
    sign_extended = { {8{in[3]}}, in };
    twos_complement = ~sign_extended + 1;
    out = twos_complement[3:0];
end

endmodule
