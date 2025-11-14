
module shift_register (
    input clk,
    input reset, // Synchronous active-high reset
    input [7:0] d, // Input for the shift register
    output [7:0] q // Output of the shift register
);

    reg [7:0] shift_reg = 0; // 8-bit shift register

    always @(posedge clk, posedge reset) begin
        if (reset) begin
            shift_reg <= 8'b0;
        end else begin
            shift_reg <= {shift_reg[6:0], d[0]};
        end
    end

    assign q = shift_reg;

endmodule
