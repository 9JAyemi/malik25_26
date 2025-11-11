module shift_and_add_multiplier (
    input clk,
    input reset,
    input [3:0] a, b,
    output reg [7:0] product
);

    reg [2:0] i; // Declare 'i' as a 3-bit register

    always @(posedge clk) begin
        if (reset) begin
            product <= 8'b0;
        end else begin
            for (i = 0; i < 4; i = i + 1) begin
                if (b[i]) begin
                    product <= product + (a << i);
                end
            end
        end
    end

endmodule