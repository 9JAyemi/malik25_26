
module twos_complement (
    input [3:0] binary_in,
    output reg [3:0] twos_comp_out
);

always @(*) begin
    twos_comp_out = ~binary_in + 1;
end

endmodule
