module top_module(
    input clk,
    input load,
    input [1:0] ena,
    input [99:0] data,
    output reg [99:0] q);

    reg [99:0] shift_reg;

    always @(posedge clk) begin
        if (load) begin
            shift_reg <= data;
        end else begin
            if (ena[0]) begin
                shift_reg <= {shift_reg[98:0], shift_reg[99]};
            end
            if (ena[1]) begin
                shift_reg <= {shift_reg[0], shift_reg[99:1]};
            end
        end
    end

    always @*
    begin
        q = shift_reg;
    end

endmodule