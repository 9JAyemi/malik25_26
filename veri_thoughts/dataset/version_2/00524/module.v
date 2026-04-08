module pwm_generator(
    input clk,
    input rst_n,
    output reg pwm_out
);

always @(posedge clk or negedge rst_n) begin
    if (~rst_n) begin
        pwm_out <= 1'b0;
    end else begin
        pwm_out <= ~pwm_out;
    end
end

endmodule