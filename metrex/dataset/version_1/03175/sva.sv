// SVA for touch_sensor_interface
// Bind example (connects to internals):
// bind touch_sensor_interface touch_sensor_interface_sva sva (.* , .cap_sense(cap_sense), .res_sense(res_sense));

module touch_sensor_interface_sva (
  input  logic sensor_type,
  input  logic touch,
  input  logic touched,
  input  logic cap_sense,
  input  logic res_sense
);

  // Environment assumption: sensor_type stable across touch edge
  assume property (@(posedge touch) $stable(sensor_type));

  // On each touch edge, exactly the selected algorithm toggles; the other holds
  assert property (@(posedge touch)
    disable iff ($isunknown(sensor_type) || $isunknown($past(cap_sense)) || $isunknown($past(res_sense)))
      sensor_type |-> (cap_sense == !$past(cap_sense) && $stable(res_sense))
  );

  assert property (@(posedge touch)
    disable iff ($isunknown(sensor_type) || $isunknown($past(cap_sense)) || $isunknown($past(res_sense)))
      !sensor_type |-> (res_sense == !$past(res_sense) && $stable(cap_sense))
  );

  // Internal regs may only change on a touch edge, and must match the selected mode on that edge
  assert property (@(posedge cap_sense or negedge cap_sense)
    $rose(touch) && $past(sensor_type, 1, posedge touch)
  );

  assert property (@(posedge res_sense or negedge res_sense)
    $rose(touch) && !$past(sensor_type, 1, posedge touch)
  );

  // Output mux correctness any time driving inputs change (same-delta check)
  assert property (@(posedge sensor_type or negedge sensor_type
                     or posedge cap_sense or negedge cap_sense
                     or posedge res_sense or negedge res_sense)
    1 |-> ##0 (touched === (sensor_type ? cap_sense : res_sense))
  );

  // Optional X-propagation sanity: when select and selected data are known, output must be known
  assert property (@(posedge sensor_type or negedge sensor_type
                     or posedge cap_sense or negedge cap_sense
                     or posedge res_sense or negedge res_sense)
    (!$isunknown(sensor_type) && !$isunknown(sensor_type ? cap_sense : res_sense))
      |-> ##0 !$isunknown(touched)
  );

  // Coverage
  cover property (@(posedge touch)
    sensor_type && (cap_sense != $past(cap_sense)) && (touched === cap_sense)
  );

  cover property (@(posedge touch)
    !sensor_type && (res_sense != $past(res_sense)) && (touched === res_sense)
  );

  // See both modes across successive touches
  cover property (@(posedge touch) sensor_type ##1 @(posedge touch) !sensor_type);
  cover property (@(posedge touch) !sensor_type ##1 @(posedge touch) sensor_type);

  // Sensor type switch immediately updates output
  cover property (@(posedge sensor_type or negedge sensor_type) ##0
    (touched === (sensor_type ? cap_sense : res_sense))
  );

endmodule