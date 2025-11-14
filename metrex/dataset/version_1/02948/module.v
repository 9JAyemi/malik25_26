
module functional_module (
    input [7:0] dff_out,
    input xnor_out,
    output reg [7:0] xor_out
);
    always @(*) begin
        xor_out = dff_out ^ xnor_out;
    end
endmodule
