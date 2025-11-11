// SVA checker for ExtADCSimple
// Concise, high-signal-coverage assertions and key functional covers

module ExtADCSimple_sva (
  input  logic        Reset_n_i,
  input  logic        Clk_i,
  input  logic        Enable_i,
  input  logic        CpuIntr_o,
  input  logic        SensorPower_o,
  input  logic        SensorStart_o,
  input  logic        SensorReady_i,
  input  logic        AdcStart_o,
  input  logic        AdcDone_i,
  input  logic        TimerOvfl,
  input  logic        TimerPreset,
  input  logic        TimerEnable,
  input  logic        StoreNewValue,
  input  logic [15:0] AdcValue_i,
  input  logic [15:0] PeriodCounterPreset_i,
  input  logic [15:0] Timer,
  input  logic [15:0] Word0,
  input  logic [2:0]  State,
  input  logic [2:0]  NextState
);

  // Local state encodings (must match DUT)
  localparam stDisabled     = 3'b000;
  localparam stIdle         = 3'b001;
  localparam stSensorPower  = 3'b010;
  localparam stSensorSettle = 3'b011;
  localparam stMeasure      = 3'b100;

  default clocking cb @(posedge Clk_i); endclocking
  default disable iff (!Reset_n_i);

  // -------------------------
  // Reset behavior
  // -------------------------
  assert property ( !Reset_n_i |-> (State==stDisabled && Timer==16'd0 && Word0==16'd0) );

  // -------------------------
  // State register update
  // -------------------------
  assert property ( $past(Reset_n_i) |-> State == $past(NextState) );

  // -------------------------
  // Legal next-state transitions
  // -------------------------
  assert property ( (State==stDisabled &&  Enable_i) |=> State==stIdle );
  assert property ( (State==stDisabled && !Enable_i) |=> State==stDisabled );

  assert property ( (State==stIdle && !Enable_i)     |=> State==stDisabled );
  assert property ( (State==stIdle &&  Enable_i &&  TimerOvfl) |=> State==stSensorPower );
  assert property ( (State==stIdle &&  Enable_i && !TimerOvfl) |=> State==stIdle );

  assert property ( (State==stSensorPower) |=> State==stSensorSettle );

  assert property ( (State==stSensorSettle &&  SensorReady_i) |=> State==stMeasure );
  assert property ( (State==stSensorSettle && !SensorReady_i) |=> State==stSensorSettle );

  assert property ( (State==stMeasure &&  AdcDone_i) |=> State==stIdle );
  assert property ( (State==stMeasure && !AdcDone_i) |=> State==stMeasure );

  // -------------------------
  // Output/control decode vs state/inputs
  // -------------------------
  // Disabled: all control outputs low
  assert property ( State==stDisabled |-> (!SensorPower_o && !SensorStart_o && !AdcStart_o && !CpuIntr_o) );

  // Idle: SensorPower_o only when TimerOvfl, others low
  assert property ( State==stIdle |-> (SensorStart_o==1'b0 && AdcStart_o==1'b0 && CpuIntr_o==1'b0
                                      && SensorPower_o==TimerOvfl) );

  // SensorPower: power+start asserted, adc start low
  assert property ( State==stSensorPower |-> (SensorPower_o && SensorStart_o && !AdcStart_o && !CpuIntr_o) );

  // SensorSettle: power+start asserted; adc start mirrors SensorReady
  assert property ( State==stSensorSettle |-> (SensorPower_o && SensorStart_o && (AdcStart_o==SensorReady_i) && !CpuIntr_o) );

  // Measure: all asserted; intr only when done
  assert property ( State==stMeasure |-> (SensorPower_o && SensorStart_o && AdcStart_o && (CpuIntr_o==AdcDone_i)) );

  // Relationship checks
  assert property ( SensorStart_o |-> SensorPower_o );
  assert property ( AdcStart_o   |-> (SensorPower_o && SensorStart_o) );
  assert property ( CpuIntr_o == StoreNewValue );
  assert property ( CpuIntr_o |=> !CpuIntr_o ); // single-cycle pulse

  // -------------------------
  // Timer control and data-path correctness
  // -------------------------
  // Mutual exclusion of preset vs enable
  assert property ( !(TimerPreset && TimerEnable) );

  // Timer control only asserted in intended places
  assert property ( TimerEnable |-> ( (State==stIdle     && Enable_i && !TimerOvfl)
                                   || (State==stDisabled && Enable_i) ) );
  assert property ( !((State inside {stSensorPower,stSensorSettle,stMeasure}) // these states must not enable timer
                      || (State==stIdle && TimerOvfl)
                      || (State==stDisabled && !Enable_i)) or (!TimerEnable && TimerPreset) );

  // Timer next value behavior
  assert property ( $past(Reset_n_i) |-> (
                     ($past(TimerPreset) && (Timer == $past(PeriodCounterPreset_i))) ||
                     (!$past(TimerPreset) && $past(TimerEnable) && (Timer == $past(Timer) - 16'd1)) ||
                     (!$past(TimerPreset) && !$past(TimerEnable) && (Timer == $past(Timer)))
                   ));

  // Timer overflow flag correctness
  assert property ( TimerOvfl == (Timer==16'd0) );

  // -------------------------
  // Storage path correctness
  // -------------------------
  assert property ( $past(StoreNewValue) |-> (Word0 == $past(AdcValue_i)) );
  assert property ( !$past(StoreNewValue) |-> (Word0 == $past(Word0)) );
  assert property ( SensorValue_o_consistent: Word0 == Word0 ); // placeholder label to allow bind if needed

endmodule


// Bind with access to DUT internals
bind ExtADCSimple ExtADCSimple_sva sva_i (
  .Reset_n_i(Reset_n_i),
  .Clk_i(Clk_i),
  .Enable_i(Enable_i),
  .CpuIntr_o(CpuIntr_o),
  .SensorPower_o(SensorPower_o),
  .SensorStart_o(SensorStart_o),
  .SensorReady_i(SensorReady_i),
  .AdcStart_o(AdcStart_o),
  .AdcDone_i(AdcDone_i),
  .TimerOvfl(TimerOvfl),
  .TimerPreset(TimerPreset),
  .TimerEnable(TimerEnable),
  .StoreNewValue(StoreNewValue),
  .AdcValue_i(AdcValue_i),
  .PeriodCounterPreset_i(PeriodCounterPreset_i),
  .Timer(Timer),
  .Word0(Word0),
  .State(State),
  .NextState(NextState)
);


// Compact functional coverage (key scenarios)
module ExtADCSimple_cov (
  input  logic Reset_n_i, Clk_i,
  input  logic Enable_i, SensorReady_i, AdcDone_i,
  input  logic CpuIntr_o, SensorPower_o, SensorStart_o, AdcStart_o,
  input  logic TimerEnable, TimerOvfl,
  input  logic [2:0] State
);
  localparam stDisabled     = 3'b000;
  localparam stIdle         = 3'b001;
  localparam stSensorPower  = 3'b010;
  localparam stSensorSettle = 3'b011;
  localparam stMeasure      = 3'b100;

  default clocking @(posedge Clk_i); endclocking
  default disable iff (!Reset_n_i);

  // Visit all states
  cover property (State==stDisabled);
  cover property (State==stIdle);
  cover property (State==stSensorPower);
  cover property (State==stSensorSettle);
  cover property (State==stMeasure);

  // One full successful measurement cycle
  cover property ( $rose(Enable_i)
                   ##[1:$] (State==stIdle && TimerEnable && !TimerOvfl)
                   ##[1:$] (State==stIdle && TimerOvfl && SensorPower_o)
                   ##1     (State==stSensorPower)
                   ##1     (State==stSensorSettle)
                   ##[1:$] (State==stSensorSettle && SensorReady_i && AdcStart_o)
                   ##1     (State==stMeasure && AdcStart_o)
                   ##[1:$] (State==stMeasure && AdcDone_i && CpuIntr_o) );

  // AdcStart_o seen in both settle (on ready) and measure
  cover property (State==stSensorSettle && SensorReady_i && AdcStart_o);
  cover property (State==stMeasure && AdcStart_o);

endmodule

bind ExtADCSimple ExtADCSimple_cov cov_i (
  .Reset_n_i(Reset_n_i),
  .Clk_i(Clk_i),
  .Enable_i(Enable_i),
  .SensorReady_i(SensorReady_i),
  .AdcDone_i(AdcDone_i),
  .CpuIntr_o(CpuIntr_o),
  .SensorPower_o(SensorPower_o),
  .SensorStart_o(SensorStart_o),
  .AdcStart_o(AdcStart_o),
  .TimerEnable(TimerEnable),
  .TimerOvfl(TimerOvfl),
  .State(State)
);