
module rotator(
    input clk,
    input load,
    input [1:0] ena,
    input [99:0] data,
    output [99:0] q
);

    reg [99:0] shift_reg;

    always @(posedge clk) begin
        if (load) begin
            shift_reg <= data;
        end else if (ena[1]) begin  // Corrected the order here
            shift_reg <= {shift_reg[98:0], shift_reg[99]};
        end else if (ena[0]) begin  // Corrected the order here
            shift_reg <= {shift_reg[1:0], shift_reg[0]};
        end
    end

    assign q = shift_reg;

endmodule
