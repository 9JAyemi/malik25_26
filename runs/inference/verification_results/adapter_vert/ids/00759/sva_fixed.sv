module robotic_arm_controller_sva (
    input logic servo1_angle,
    input logic servo1_pwm,
    input logic servo2_angle,
    input logic servo2_pwm,
    input logic servo3_angle,
    input logic servo3_pwm,
    input logic servo4_angle,
    input logic servo4_pwm,
    input logic servo5_angle,
    input logic servo5_pwm,
    input logic clk_in_1
);

property ServoSynceotid; @(posedge clk_in_1) (servo1_angle) |-> (servo1_pwm) == ( (servo1_angle * 11) + 500 ); endproperty
assert property (ServoSynceotid);

property ServoSynceotid_2; @(posedge clk_in_1) (servo2_angle) |-> (servo2_pwm) == ( (servo2_angle * 11) + 500 ); endproperty
assert property (ServoSynceotid_2);

property ServoSynceotid_3; @(posedge clk_in_1) (servo3_angle) |-> (servo3_pwm) == ( (servo3_angle * 11) + 500 ); endproperty
assert property (ServoSynceotid_3);

property ServoSynceotid_4; @(posedge clk_in_1) (servo4_angle) |-> (servo4_pwm) == ( (servo4_angle * 11) + 500 ); endproperty
assert property (ServoSynceotid_4);

property ServoSynceotid_5; @(posedge clk_in_1) (servo5_angle) |-> (servo5_pwm) == ( (servo5_angle * 11) + 500 ); endproperty
assert property (ServoSynceotid_5);

endmodule