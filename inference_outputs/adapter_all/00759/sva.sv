module robotic_arm_controller_sva (
    input logic        clk,
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

    // servo1_pwm must match the implemented linear mapping.
    check_servo1_pwm_mapping: assert property (
        @(posedge clk) servo1_pwm == ((servo1_angle * 11) + 500)
    );

    // servo2_pwm must match the implemented linear mapping.
    check_servo2_pwm_mapping: assert property (
        @(posedge clk) servo2_pwm == ((servo2_angle * 11) + 500)
    );

    // servo3_pwm must match the implemented linear mapping.
    check_servo3_pwm_mapping: assert property (
        @(posedge clk) servo3_pwm == ((servo3_angle * 11) + 500)
    );

    // servo4_pwm must match the implemented linear mapping.
    check_servo4_pwm_mapping: assert property (
        @(posedge clk) servo4_pwm == ((servo4_angle * 11) + 500)
    );

    // servo5_pwm must match the implemented linear mapping.
    check_servo5_pwm_mapping: assert property (
        @(posedge clk) servo5_pwm == ((servo5_angle * 11) + 500)
    );

    // servo1_pwm must be within the implemented output range.
    check_servo1_pwm_range: assert property (
        @(posedge clk) servo1_pwm <= 12'd1650
    );

    // servo2_pwm must be within the implemented output range.
    check_servo2_pwm_range: assert property (
        @(posedge clk) servo2_pwm <= 12'd1650
    );

    // servo3_pwm must be within the implemented output range.
    check_servo3_pwm_range: assert property (
        @(posedge clk) servo3_pwm <= 12'd1650
    );

    // servo4_pwm must be within the implemented output range.
    check_servo4_pwm_range: assert property (
        @(posedge clk) servo4_pwm <= 12'd1650
    );

    // servo5_pwm must be within the implemented output range.
    check_servo5_pwm_range: assert property (
        @(posedge clk) servo5_pwm <= 12'd1650
    );

endmodule