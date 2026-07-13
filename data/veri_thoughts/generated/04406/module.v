
module ring_delay (
    input clk,
    input d,
    input [3:0] delay,
    output reg q
);

reg [2:0] shift_reg;
reg [3:0] delay_counter;

always @(posedge clk) begin
    // Shift the register
    shift_reg <= {shift_reg[1:0], d};

    // Update the delay counter
    if (delay_counter == delay) begin
        // Output the delayed value
        q <= shift_reg[2];
        delay_counter <= 0;
    end else begin
        delay_counter <= delay_counter + 1;
    end
end

endmodule
