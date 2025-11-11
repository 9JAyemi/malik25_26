// SVA for module ring
module ring_sva
  #(parameter WIDTH=32, ALARM_STEP=24)
  (input  logic [WIDTH-1:0] clk_src,
   input  logic             power,
   input  logic             weight_ch,
   input  logic             mode_ch,
   input  logic [2:0]       w_r_d_end,
   input  logic             alarm,
   input  logic [WIDTH-1:0] count,
   input  logic [1:0]       state,
   input  logic [1:0]       next_state);

  localparam int NO_ALARM   = 0;
  localparam int BTN_ALARM  = 1;
  localparam int PHASE_ALARM= 2;

  // Elaboration/runtime sanity
  initial assert (ALARM_STEP < WIDTH) else $fatal(1,"ALARM_STEP out of range");
  initial assert (alarm==0 && count==0 && state==NO_ALARM && next_state==NO_ALARM)
    else $error("Initial values mismatch");

  // Known/valid encodings
  assert property (@(posedge clk_src[ALARM_STEP]) !$isunknown({power,mode_ch,weight_ch,w_r_d_end,alarm,state,next_state}));
  assert property (@(posedge clk_src[ALARM_STEP]) state inside {NO_ALARM,BTN_ALARM,PHASE_ALARM});
  assert property (@(posedge clk_src[ALARM_STEP]) next_state inside {NO_ALARM,BTN_ALARM,PHASE_ALARM});

  // State register update on clk_src[0]
  assert property (@(posedge clk_src[0] or negedge clk_src[0]) power  |-> ##0 state == next_state);
  assert property (@(posedge clk_src[0] or negedge clk_src[0]) !power |-> ##0 state == NO_ALARM);

  // next_state forced when !power
  assert property (@(posedge clk_src[ALARM_STEP]) !power |-> ##0 next_state == NO_ALARM);

  // next_state function when power==1
  // NO_ALARM
  assert property (@(posedge clk_src[ALARM_STEP])
    power && state==NO_ALARM && (mode_ch || weight_ch) |-> ##0 next_state==BTN_ALARM);
  assert property (@(posedge clk_src[ALARM_STEP])
    power && state==NO_ALARM && !(mode_ch || weight_ch) && (w_r_d_end!=3'b000) |-> ##0 next_state==PHASE_ALARM);
  assert property (@(posedge clk_src[ALARM_STEP])
    power && state==NO_ALARM && !(mode_ch || weight_ch) && (w_r_d_end==3'b000) |-> ##0 next_state==NO_ALARM);

  // BTN_ALARM
  assert property (@(posedge clk_src[ALARM_STEP])
    power && state==BTN_ALARM && (w_r_d_end!=3'b000) |-> ##0 next_state==PHASE_ALARM);
  assert property (@(posedge clk_src[ALARM_STEP])
    power && state==BTN_ALARM && (w_r_d_end==3'b000) && (count>=2) |-> ##0 next_state==NO_ALARM);
  assert property (@(posedge clk_src[ALARM_STEP])
    power && state==BTN_ALARM && (w_r_d_end==3'b000) && (count<2)  |-> ##0 next_state==BTN_ALARM);

  // PHASE_ALARM
  assert property (@(posedge clk_src[ALARM_STEP])
    power && state==PHASE_ALARM && (mode_ch || weight_ch) |-> ##0 next_state==BTN_ALARM);
  assert property (@(posedge clk_src[ALARM_STEP])
    power && state==PHASE_ALARM && !(mode_ch || weight_ch) && (count>=6) |-> ##0 next_state==NO_ALARM);
  assert property (@(posedge clk_src[ALARM_STEP])
    power && state==PHASE_ALARM && !(mode_ch || weight_ch) && (count<6)  |-> ##0 next_state==PHASE_ALARM);

  // Output/count behavior on clk_src[ALARM_STEP]
  assert property (@(posedge clk_src[ALARM_STEP])
    state==NO_ALARM |-> ##0 (count==0 && alarm==0));
  assert property (@(posedge clk_src[ALARM_STEP])
    (state==BTN_ALARM || state==PHASE_ALARM) |-> ##0 (count==$past(count)+1 && alarm!=$past(alarm)));

  // Key coverage
  cover property (@(posedge clk_src[ALARM_STEP]) power && state==NO_ALARM && mode_ch);
  cover property (@(posedge clk_src[ALARM_STEP]) power && state==NO_ALARM && w_r_d_end!=3'b000);
  cover property (@(posedge clk_src[ALARM_STEP]) power && state==BTN_ALARM  && count==2);
  cover property (@(posedge clk_src[ALARM_STEP]) power && state==PHASE_ALARM&& count==6);
  cover property (@(posedge clk_src[ALARM_STEP]) (state==BTN_ALARM || state==PHASE_ALARM) && alarm!=$past(alarm));
endmodule

// Bind into DUT (accesses internal regs state/next_state/count)
bind ring ring_sva #(.WIDTH(WIDTH), .ALARM_STEP(ALARM_STEP)) u_ring_sva (
  .clk_src(clk_src),
  .power(power),
  .weight_ch(weight_ch),
  .mode_ch(mode_ch),
  .w_r_d_end(w_r_d_end),
  .alarm(alarm),
  .count(count),
  .state(state),
  .next_state(next_state)
);