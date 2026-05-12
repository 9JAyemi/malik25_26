property ServoSynceotid; @(posedge clk_in_1) (servo1_angle) |-> (servo1_pwm) == ( (servo1_angle * 11) + 500 ); endproperty 
 
 property ServoSynceotid; @(posedge clk_in_1) (servo2_angle) |-> (servo2_pwm) == ( (servo2_angle * 11) + 500 ); endproperty 
 
 property ServoSynceotid; @(posedge clk_in_1) (servo3_angle) |-> (servo3_pwm) == ( (servo3_angle * 11) + 500 ); endproperty 
 
 property ServoSynceotid; @(posedge clk_in_1) (servo4_angle) |-> (servo4_pwm) == ( (servo4_angle * 11) + 500 ); endproperty 
 
 property ServoSynceotid; @(posedge clk_in_1) (servo5_angle) |-> (servo5_pwm) == ( (servo5_angle * 11) + 500 ); endproperty 
 