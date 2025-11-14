// SVA checker for robotic_arm_controller
// Bind this module to the DUT and drive clk from your TB.
// Example bind: bind robotic_arm_controller robotic_arm_controller_sva sva_i (.*,.clk(tb_clk));

module robotic_arm_controller_sva (
  input logic clk,

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

  default clocking cb @(posedge clk); endclocking

  // Past-valid guard for temporal checks
  logic past_valid;
  initial past_valid = 1'b0;
  always @(posedge clk) past_valid <= 1'b1;

  // Functional mapping
  function automatic int pwm_calc (input logic [7:0] a);
    return int'(a)*11 + 500;
  endfunction

  // Common assumptions: angles are known
  assume property (!$isunknown({servo1_angle,servo2_angle,servo3_angle,servo4_angle,servo5_angle}));

  // Macro to keep assertions concise per servo
`define SERVO_ASSERTS(ID) \
  /* Exact function check each sample */ \
  assert property (int'(servo``ID``_pwm) == pwm_calc(servo``ID``_angle)); \
  /* Legal range check (12-bit safe) */ \
  assert property (servo``ID``_pwm inside {[12'd500:12'd3305]}); \
  /* Output changes only if its own angle changes (no cross-coupling) */ \
  assert property ($changed(servo``ID``_pwm) |-> $changed(servo``ID``_angle)); \
  /* Linearity over time: delta_pwm = 11 * delta_angle */ \
  assert property (disable iff (!past_valid) \
                   $changed(servo``ID``_angle) |-> \
                   (int'(servo``ID``_pwm) - int'($past(servo``ID``_pwm))) \
                   == 11*(int'(servo``ID``_angle) - int'($past(servo``ID``_angle)))); \
  /* Corner coverage */ \
  cover property (servo``ID``_angle==8'd0   && servo``ID``_pwm==12'd500); \
  cover property (servo``ID``_angle==8'd255 && servo``ID``_pwm==12'd3305); \
  /* Slope step coverage (+1 angle -> +11 pwm) */ \
  cover property (disable iff (!past_valid) \
                  (servo``ID``_angle == $past(servo``ID``_angle)+1) && \
                  (int'(servo``ID``_pwm) == int'($past(servo``ID``_pwm))+11));

  `SERVO_ASSERTS(1)
  `SERVO_ASSERTS(2)
  `SERVO_ASSERTS(3)
  `SERVO_ASSERTS(4)
  `SERVO_ASSERTS(5)

  // Independence: a change on one angle with others stable must not perturb other PWMs
  assert property ($changed(servo1_angle) && $stable({servo2_angle,servo3_angle,servo4_angle,servo5_angle})
                   |-> $stable({servo2_pwm,servo3_pwm,servo4_pwm,servo5_pwm}));
  assert property ($changed(servo2_angle) && $stable({servo1_angle,servo3_angle,servo4_angle,servo5_angle})
                   |-> $stable({servo1_pwm,servo3_pwm,servo4_pwm,servo5_pwm}));
  assert property ($changed(servo3_angle) && $stable({servo1_angle,servo2_angle,servo4_angle,servo5_angle})
                   |-> $stable({servo1_pwm,servo2_pwm,servo4_pwm,servo5_pwm}));
  assert property ($changed(servo4_angle) && $stable({servo1_angle,servo2_angle,servo3_angle,servo5_angle})
                   |-> $stable({servo1_pwm,servo2_pwm,servo3_pwm,servo5_pwm}));
  assert property ($changed(servo5_angle) && $stable({servo1_angle,servo2_angle,servo3_angle,servo4_angle})
                   |-> $stable({servo1_pwm,servo2_pwm,servo3_pwm,servo4_pwm}));

  // Coverage: exercise independent change scenarios
  cover property ($changed(servo1_angle) && $stable({servo2_angle,servo3_angle,servo4_angle,servo5_angle}));
  cover property ($changed(servo2_angle) && $stable({servo1_angle,servo3_angle,servo4_angle,servo5_angle}));
  cover property ($changed(servo3_angle) && $stable({servo1_angle,servo2_angle,servo4_angle,servo5_angle}));
  cover property ($changed(servo4_angle) && $stable({servo1_angle,servo2_angle,servo3_angle,servo5_angle}));
  cover property ($changed(servo5_angle) && $stable({servo1_angle,servo2_angle,servo3_angle,servo4_angle}));

endmodule