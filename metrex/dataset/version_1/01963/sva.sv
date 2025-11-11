// SVA for traffic_light
// Bind into DUT to access internals (state, timer, currents)
module traffic_light_sva;

  default clocking cb @(posedge clk); endclocking

  // Reset behavior
  ap_reset: assert property (cb
    reset |=> state==S0 && timer==0 &&
    current_road1_lane==2'b00 && current_road2_lane==2'b00 &&
    traffic_light_road1==4'b0100 && traffic_light_road2==4'b0100 &&
    pedestrian_light==1'b0
  );

  // Legal state encoding
  ap_state_legal: assert property (cb
    disable iff (reset)
    state inside {S0,S1,S2,S3}
  );

  // No illegal light encodings (no 2'b11)
  ap_no_illegal_lights: assert property (cb
    disable iff (reset)
    traffic_light_road1[3:2] != 2'b11 && traffic_light_road1[1:0] != 2'b11 &&
    traffic_light_road2[3:2] != 2'b11 && traffic_light_road2[1:0] != 2'b11
  );

  // Timer decrements when previously > 0
  ap_timer_dec: assert property (cb
    disable iff (reset)
    $past(timer)>0 |-> timer == $past(timer)-1
  );

  // When counting (past timer>0), state and outputs/regs hold
  ap_hold_state_when_tgt0: assert property (cb
    disable iff (reset)
    $past(timer)>0 |-> state == $past(state)
  );
  ap_hold_outputs_when_tgt0: assert property (cb
    disable iff (reset)
    $past(timer)>0 |-> traffic_light_road1==$past(traffic_light_road1) &&
                       traffic_light_road2==$past(traffic_light_road2) &&
                       pedestrian_light==$past(pedestrian_light) &&
                       current_road1_lane==$past(current_road1_lane) &&
                       current_road2_lane==$past(current_road2_lane)
  );

  // In-state invariants while timer>0
  ap_S0_inv: assert property (cb
    disable iff (reset)
    state==S0 && timer>0 |-> traffic_light_road1==4'b0100 && traffic_light_road2==4'b0100 && !pedestrian_light
  );
  ap_S1_inv: assert property (cb
    disable iff (reset)
    state==S1 && timer>0 |-> traffic_light_road1=={2'b10,2'b01} && traffic_light_road2=={2'b00,2'b10}
  );
  ap_S2_inv: assert property (cb
    disable iff (reset)
    state==S2 && timer>0 |-> traffic_light_road1=={2'b10,2'b00} && traffic_light_road2=={2'b01,2'b00}
  );
  ap_S3_inv: assert property (cb
    disable iff (reset)
    state==S3 && timer>0 |-> traffic_light_road1=={2'b00,2'b10} && traffic_light_road2=={2'b10,2'b01} && pedestrian_light
  );

  // Transitions on timer==0
  ap_S0_to_S1_ped: assert property (cb
    disable iff (reset)
    state==S0 && timer==0 && pedestrian_sensor |=> 
      state==S1 && timer==PEDESTRIAN_TIME && pedestrian_light &&
      traffic_light_road1=={2'b10,2'b01} && traffic_light_road2=={2'b00,2'b10}
  );

  ap_S0_to_S1_car1: assert property (cb
    disable iff (reset)
    state==S0 && timer==0 && !pedestrian_sensor &&
    (car_sensor_road1_lane1 || car_sensor_road1_lane2) |=> 
      state==S1 && timer==GREEN_TIME && current_road1_lane==2'b01 &&
      traffic_light_road1=={2'b10,2'b01} && traffic_light_road2=={2'b00,2'b10}
  );

  ap_S0_to_S2_car2: assert property (cb
    disable iff (reset)
    state==S0 && timer==0 && !pedestrian_sensor &&
    !(car_sensor_road1_lane1 || car_sensor_road1_lane2) &&
    (car_sensor_road2_lane1 || car_sensor_road2_lane2) |=> 
      state==S2 && timer==YELLOW_TIME &&
      traffic_light_road1=={2'b10,2'b00} && traffic_light_road2=={2'b01,2'b00}
  );

  ap_S0_hold_idle: assert property (cb
    disable iff (reset)
    state==S0 && timer==0 && !pedestrian_sensor &&
    !(car_sensor_road1_lane1 || car_sensor_road1_lane2) &&
    !(car_sensor_road2_lane1 || car_sensor_road2_lane2) |=> 
      state==S0 && timer==0 &&
      traffic_light_road1==$past(traffic_light_road1) &&
      traffic_light_road2==$past(traffic_light_road2) &&
      pedestrian_light==$past(pedestrian_light)
  );

  ap_S1_to_S2: assert property (cb
    disable iff (reset)
    state==S1 && timer==0 |=> 
      state==S2 && timer==YELLOW_TIME &&
      traffic_light_road1=={2'b10,2'b00} && traffic_light_road2=={2'b01,2'b00}
  );

  ap_S2_to_S3_ped: assert property (cb
    disable iff (reset)
    state==S2 && timer==0 && pedestrian_sensor |=> 
      state==S3 && timer==PEDESTRIAN_TIME && pedestrian_light &&
      traffic_light_road1=={2'b00,2'b10} && traffic_light_road2=={2'b10,2'b01}
  );

  ap_S2_to_S3_car2: assert property (cb
    disable iff (reset)
    state==S2 && timer==0 && !pedestrian_sensor &&
    (car_sensor_road2_lane1 || car_sensor_road2_lane2) |=> 
      state==S3 && timer==GREEN_TIME && current_road2_lane==2'b01 &&
      traffic_light_road1=={2'b00,2'b10} && traffic_light_road2=={2'b10,2'b01}
  );

  ap_S2_to_S1_car1: assert property (cb
    disable iff (reset)
    state==S2 && timer==0 && !pedestrian_sensor &&
    !(car_sensor_road2_lane1 || car_sensor_road2_lane2) &&
    (car_sensor_road1_lane1 || car_sensor_road1_lane2) |=> 
      state==S1 && timer==YELLOW_TIME &&
      traffic_light_road1=={2'b10,2'b01} && traffic_light_road2=={2'b00,2'b10}
  );

  ap_S2_hold_idle: assert property (cb
    disable iff (reset)
    state==S2 && timer==0 && !pedestrian_sensor &&
    !(car_sensor_road1_lane1 || car_sensor_road1_lane2) &&
    !(car_sensor_road2_lane1 || car_sensor_road2_lane2) |=> 
      state==S2 && timer==0 &&
      traffic_light_road1==$past(traffic_light_road1) &&
      traffic_light_road2==$past(traffic_light_road2) &&
      pedestrian_light==$past(pedestrian_light)
  );

  ap_S3_to_S0: assert property (cb
    disable iff (reset)
    state==S3 && timer==0 |=> 
      state==S0 && timer==YELLOW_TIME &&
      traffic_light_road1==4'b0100 && traffic_light_road2==4'b0100 && !pedestrian_light
  );

  // Lane registers only update on their designated transitions
  ap_current_r1_update_only: assert property (cb
    disable iff (reset)
    (current_road1_lane != $past(current_road1_lane)) |->
      ($past(state)==S0 && $past(timer)==0 && !$past(pedestrian_sensor) &&
       ($past(car_sensor_road1_lane1)||$past(car_sensor_road1_lane2)))
  );
  ap_current_r2_update_only: assert property (cb
    disable iff (reset)
    (current_road2_lane != $past(current_road2_lane)) |->
      ($past(state)==S2 && $past(timer)==0 && !$past(pedestrian_sensor) &&
       ($past(car_sensor_road2_lane1)||$past(car_sensor_road2_lane2)))
  );

  // Coverage: all branches and timer count-downs
  cv_S0_S1_ped:  cover property (cb state==S0 && timer==0 && pedestrian_sensor ##1 state==S1);
  cv_S0_S1_car1: cover property (cb state==S0 && timer==0 && (car_sensor_road1_lane1 || car_sensor_road1_lane2) ##1 state==S1);
  cv_S0_S2_car2: cover property (cb state==S0 && timer==0 && !(car_sensor_road1_lane1 || car_sensor_road1_lane2) &&
                                      (car_sensor_road2_lane1 || car_sensor_road2_lane2) ##1 state==S2);
  cv_S1_S2:      cover property (cb state==S1 && timer==0 ##1 state==S2);
  cv_S2_S3_ped:  cover property (cb state==S2 && timer==0 && pedestrian_sensor ##1 state==S3);
  cv_S2_S3_car2: cover property (cb state==S2 && timer==0 && !pedestrian_sensor &&
                                      (car_sensor_road2_lane1 || car_sensor_road2_lane2) ##1 state==S3);
  cv_S2_S1_car1: cover property (cb state==S2 && timer==0 && !pedestrian_sensor &&
                                      (car_sensor_road1_lane1 || car_sensor_road1_lane2) ##1 state==S1);
  cv_S3_S0:      cover property (cb state==S3 && timer==0 ##1 state==S0);

  // Generic timer countdown coverage for all programmed loads
  cv_green_countdown:   cover property (cb timer==GREEN_TIME       ##[GREEN_TIME]       timer==0);
  cv_ped_countdown:     cover property (cb timer==PEDESTRIAN_TIME  ##[PEDESTRIAN_TIME]  timer==0);
  cv_yellow_countdown:  cover property (cb timer==YELLOW_TIME      ##[YELLOW_TIME]      timer==0);

endmodule

bind traffic_light traffic_light_sva;