
module adder(
    input wire clk,
    input wire reset_n,
    input wire [7:0] a,
    input wire [7:0] b,
    output wire [7:0] sum,
    output wire carry
);

    reg [8:0] temp_sum;
    reg carry_reg;
    
    always @ (posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            temp_sum <= 0;
            carry_reg <= 0;
        end else begin
            {carry_reg, temp_sum} <= a + b;
        end
    end
    
    assign carry = carry_reg;
    assign sum = temp_sum[7:0];

endmodule
