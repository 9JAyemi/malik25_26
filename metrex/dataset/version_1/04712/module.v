
module Booth_Multiplier(
    input signed [3:0] multiplicand,
    input signed [3:0] multiplier,
    input clock,
    input start,
    output signed [7:0] product,
    output busy
);

reg signed [7:0] product_reg;
reg [2:0] state;
reg busy_reg;

always @(posedge clock) begin
    case(state)
        3'b000: begin
            product_reg <= 8'b00000000;
            state <= 3'b001;
        end
        3'b001: begin
            if(start) begin
                busy_reg <= 1;
                state <= 3'b010;
            end
        end
        3'b010: begin
            if(multiplier[0] == 1) begin
                product_reg <= product_reg - multiplicand;
            end else if(multiplier[0] == 0) begin
                product_reg <= product_reg + multiplicand;
            end
            state <= 3'b011;
        end
        3'b011: begin
            state <= 3'b100;
        end
        3'b100: begin
            if(multiplier == 4'b0000) begin
                state <= 3'b001;
                busy_reg <= 0;
            end else begin
                state <= 3'b010;
            end
        end
    endcase
end

assign product = product_reg;
assign busy = busy_reg;

endmodule