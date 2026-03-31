module robotic_arm_controller_sva (
    input logic clk,
    input logic [7:0] servo1_angle,
    input logic [7:0] servo2_angle,
    input logic [7:0] servo3_angle,
    input logic [7:0] servo4_angle,
    input logic [7:0] servo5_angle,
    input logic [11:0] servo1_pwm,
    input logic [11:0] servo2_pwm,
    input logic [11:0] servo3_pwm,
    input logic [11:0] servo4_pwm,
    input logic [11:0] servo5_pwm
);

// servo1_pwm equals 11*servo1_angle + 500.
    check_servo1_map: assert property (
        @(posedge clk) disable iff (1'b0)
        servo1_pwm == ((servo1_angle * 11) + 500)
    );

// servo2_pwm equals 11*servo2_angle + 500.
    check_servo2_map: assert property (
        @(posedge clk) disable iff (1'b0)
        servo2_pwm == ((servo2_angle * 11) + 500)
    );

// servo3_pwm equals 11*servo3_angle + 500.
    check_servo3_map: assert property (
        @(posedge clk) disable iff (1'b0)
        servo3_pwm == ((servo3_angle * 11) + 500)
    );

// servo4_pwm equals 11*servo4_angle + 500.
    check_servo4_map: assert property (
        @(posedge clk) disable iff (1'b0)
        servo4_pwm == ((servo4_angle * 11) + 500)
    );

// servo5_pwm equals 11*servo5_angle + 500.
    check_servo5_map: assert property (
        @(posedge clk) disable iff (1'b0)
        servo5_pwm == ((servo5_angle * 11) + 500)
    );

// All PWM outputs are within 500..2000 (11*0+500..11*180+500).
    check_pwm_range: assert property (
        @(posedge clk) disable iff (1'b0)
        (servo1_pwm >= 12'd500) && (servo1_pwm <= 12'd2000) &&
        (servo2_pwm >= 12'd500) && (servo2_pwm <= 12'd2000) &&
        (servo3_pwm >= 12'd500) && (servo3_pwm <= 12'd2000) &&
        (servo4_pwm >= 12'd500) && (servo4_pwm <= 12'd2000) &&
        (servo5_pwm >= 12'd500) && (servo5_pwm <= 12'd2000)
    );

endmodule
