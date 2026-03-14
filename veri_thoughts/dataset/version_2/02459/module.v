module shift_register (
    input in,
    output reg [2:0] out,
    input clk // Added the clk input port
);

reg [2:0] reg_out;

always @(posedge clk) begin
    reg_out <= {reg_out[1:0], in};
end

// Corrected the output assignment to use a register assignment
always @(*) begin
    out <= reg_out & 3'b111;
end

endmodule