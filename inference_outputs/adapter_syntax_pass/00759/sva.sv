module robotic_arm_controller_sva (
    input logic [7:0]  servo1_angle,
    input logic [7:0]  servo2_angle,
    input logic [7:0]  servo3_angle,
    input logic [7:0]  servo4_angle,
    input logic [7:0]  servo5_angle,
    input logic [11:0] servo1_pwm,
    input logic [11:0] servo2_pwm,
    input logic [11:0] servo3_pwm,
    input logic [11:0] servo4_pwm,
    input logic [11:0] servo5_pwm
);

    // servo1_pwm must equal the RTL's linear mapping of servo1_angle.
    check_servo1_pwm_mapping: assert property (
        @($global_clock)
        servo1_pwm == ((servo1_angle * 11) + 500)
    );

    // servo2_pwm must equal the RTL's linear mapping of servo2_angle.
    check_servo2_pwm_mapping: assert property (
        @($global_clock)
        servo2_pwm == ((servo2_angle * 11) + 500)
    );

    // servo3_pwm must equal the RTL's linear mapping of servo3_angle.
    check_servo3_pwm_mapping: assert property (
        @($global_clock)
        servo3_pwm == ((servo3_angle * 11) + 500)
    );

    // servo4_pwm must equal the RTL's linear mapping of servo4_angle.
    check_servo4_pwm_mapping: assert property (
        @($global_clock)
        servo4_pwm == ((servo4_angle * 11) + 500)
    );

    // servo5_pwm must equal the RTL's linear mapping of servo5_angle.
    check_servo5_pwm_mapping: assert property (
        @($global_clock)
        servo5_pwm == ((servo5_angle * 11) + 500)
    );

    // servo1_pwm must be within the 12-bit PWM range for all valid angles.
    check_servo1_pwm_range: assert property (
        @($global_clock)
        servo1_pwm <= 12'd4095
    );

    // servo2_pwm must be within the 12-bit PWM range for all valid angles.
    check_servo2_pwm_range: assert property (
        @($global_clock)
        servo2_pwm <= 12'd4095
    );

    // servo3_pwm must be within the 12-bit PWM range for all valid angles.
    check_servo3_pwm_range: assert property (
        @($global_clock)
        servo3_pwm <= 12'd4095
    );

    // servo4_pwm must be within the 12-bit PWM range for all valid angles.
    check_servo4_pwm_range: assert property (
        @($global_clock)
        servo4_pwm <= 12'd4095
    );

    // servo5_pwm must be within the 12-bit PWM range for all valid angles.
    check_servo5_pwm_range: assert property (
        @($global_clock)
        servo5_pwm <= 12'd4095
    );

endmodule