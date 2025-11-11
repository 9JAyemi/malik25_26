
module pwm(clk,rst,pwm_duty,pwm_offset,pwm_out);
input clk;input rst;input [7:0] pwm_duty;input [7:0] pwm_offset;output pwm_out;reg pwm_buffer;reg [7:0] counter;

parameter [7:0] PWM_DEFAULT = 8'd150;
wire [7:0] duty_temp;
wire [7:0] duty_check;

assign duty_temp = pwm_duty + ( pwm_offset - PWM_DEFAULT );assign duty_check = ( duty_temp >= 50 && duty_temp <= 250) ? duty_temp : PWM_DEFAULT;always @ (posedge clk or posedge rst)
    if(rst)
        begin
            counter <= 0;
            pwm_buffer <= 1;
        end
    else
        begin
            if( counter <= duty_check )
                begin
                    pwm_buffer <= 1;
                    counter <= counter + 1;
                end
            else
                begin
                    pwm_buffer <= 0;
                    counter <= counter;end
        end
        
    assign pwm_out = pwm_buffer;

endmodule
