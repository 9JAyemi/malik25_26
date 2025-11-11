
module shift_register_d_ff (
    input clk,
    input d,
    output [2:0] shift_register_out,
    output q
);

reg [2:0] shift_register;

assign shift_register_out = shift_register[2];
assign q = shift_register[0];

always @(posedge clk) begin
    shift_register <= {shift_register[1], shift_register[2], shift_register[0] ^ shift_register[2]};
end

endmodule
