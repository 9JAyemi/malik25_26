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
    // Servo1 PWM equals (angle * 11) + 500.
    check_servo1_mapping: assert property (
        @(posedge clk) servo1_pwm == ((servo1_angle * 8'd11) + 12'd500)
    );

    // Servo2 PWM equals (angle * 11) + 500.
    check_servo2_mapping: assert property (
        @(posedge clk) servo2_pwm == ((servo2_angle * 8'd11) + 12'd500)
    );

    // Servo3 PWM equals (angle * 11) + 500.
    check_servo3_mapping: assert property (
        @(posedge clk) servo3_pwm == ((servo3_angle * 8'd11) + 12'd500)
    );

    // Servo4 PWM equals (angle * 11) + 500.
    check_servo4_mapping: assert property (
        @(posedge clk) servo4_pwm == ((servo4_angle * 8'd11) + 12'd500)
    );

    // Servo5 PWM equals (angle * 11) + 500.
    check_servo5_mapping: assert property (
        @(posedge clk) servo5_pwm == ((servo5_angle * 8'd11) + 12'd500)
    );

    // Servo1 PWM is never below 500.
    check_servo1_min_bound: assert property (
        @(posedge clk) servo1_pwm >= 12'd500
    );

    // Servo2 PWM is never below 500.
    check_servo2_min_bound: assert property (
        @(posedge clk) servo2_pwm >= 12'd500
    );

    // Servo3 PWM is never below 500.
    check_servo3_min_bound: assert property (
        @(posedge clk) servo3_pwm >= 12'd500
    );

    // Servo4 PWM is never below 500.
    check_servo4_min_bound: assert property (
        @(posedge clk) servo4_pwm >= 12'd500
    );

    // Servo5 PWM is never below 500.
    check_servo5_min_bound: assert property (
        @(posedge clk) servo5_pwm >= 12'd500
    );
endmodule