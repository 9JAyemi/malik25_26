module Bit_Counter(
    input clk,
    input reset,
    input bit_clk_rising_edge,
    input bit_clk_falling_edge,
    input left_right_clk_rising_edge,
    input left_right_clk_falling_edge,
    output reg counting
);

parameter BIT_COUNTER_INIT = 5'd31;

reg [4:0] bit_counter;
wire reset_bit_counter;

always @(posedge clk) begin
    if (reset == 1'b1) begin
        bit_counter <= 5'h00;
    end else if (reset_bit_counter == 1'b1) begin
        bit_counter <= BIT_COUNTER_INIT;
    end else if ((bit_clk_falling_edge == 1'b1) && (bit_counter != 5'h00)) begin
        bit_counter <= bit_counter - 5'h01;
    end
end

always @(posedge clk) begin
    if (reset == 1'b1) begin
        counting <= 1'b0;
    end else if (reset_bit_counter == 1'b1) begin
        counting <= 1'b1;
    end else if ((bit_clk_falling_edge == 1'b1) && (bit_counter == 5'h00)) begin
        counting <= 1'b0;
    end
end

assign reset_bit_counter = left_right_clk_rising_edge | 
                            left_right_clk_falling_edge;

endmodule