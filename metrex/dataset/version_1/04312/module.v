module pwm_generator
    #(parameter PWM_DEPTH = 8)
    (
     input clk,
     input rst_n,
     input enable,
     input [PWM_DEPTH - 1:0] duty_cycle,
     output reg PWM_out
    );

    reg [PWM_DEPTH - 1:0] counter;
    reg [PWM_DEPTH - 1:0] threshold;

    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            counter <= 0;
            PWM_out <= 0;
        end
        else if (enable) begin
            counter <= counter + 1;
            if (counter >= threshold) begin
                counter <= 0;
                PWM_out <= 1;
            end
            else begin
                PWM_out <= 0;
            end
        end
    end

    always @(*) begin
        threshold = (2**PWM_DEPTH - 1) * duty_cycle / 100;
    end

endmodule