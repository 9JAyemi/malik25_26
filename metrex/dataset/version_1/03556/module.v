module pwm_generator(
    input clk,
    input rst,
    input input_signal,
    output reg pwm_signal
);

reg [6:0] duty_cycle;

always @(posedge clk) begin
    if (rst) begin
        pwm_signal <= 1'b0;
        duty_cycle <= 7'b0000000;
    end else begin
        if (duty_cycle == 7'b1111111) begin
            pwm_signal <= 1'b1;
        end else begin
            pwm_signal <= 1'b1;
            if (duty_cycle < 7'b1111111) begin
                duty_cycle <= duty_cycle + 1;
            end
        end
    end
end

endmodule