// SVA for edge_detector. Bind into DUT; concise but thorough.

module edge_detector_sva #(
  parameter IDLE   = 2'b00,
  parameter DETECT = 2'b01,
  parameter OUTPUT = 2'b10
)(
  input  logic        clk,
  input  logic [7:0]  in,
  input  logic [7:0]  anyedge,
  input  logic [1:0]  state,
  input  logic [7:0]  curr_in,
  input  logic [7:0]  prev_in,
  input  logic [7:0]  edge_detected
);

  default clocking cb @(posedge clk); endclocking
  default disable iff ($isunknown({state,curr_in,prev_in,in,edge_detected,anyedge}));

  function automatic [7:0] rise_mask(input [7:0] c, input [7:0] p);
    return c & ~p;
  endfunction

  // FSM encoding and legal transitions
  a_state_legal:       assert property (state inside {IDLE, DETECT, OUTPUT});
  a_idle_to_detect:    assert property (state==IDLE   |=> state==DETECT);
  a_output_to_idle:    assert property (state==OUTPUT |=> state==IDLE);
  a_detect_to_output:  assert property (state==DETECT && (curr_in!=prev_in) |=> state==OUTPUT);
  a_detect_to_idle:    assert property (state==DETECT && (curr_in==prev_in) |=> state==IDLE);

  // Pipeline/captures
  a_idle_caps:   assert property (state==IDLE
                                  |=> curr_in==$past(in)
                                   && prev_in==$past(curr_in)
                                   && edge_detected==8'h00);
  a_detect_caps: assert property (state==DETECT
                                  |=> curr_in==$past(in)
                                   && prev_in==$past(curr_in));

  // Detect math and output timing
  a_detect_math: assert property (state==DETECT && (curr_in!=prev_in)
                                  |=> edge_detected==$past(rise_mask(curr_in,prev_in)));
  a_output_eq_ed:assert property (state==OUTPUT
                                  |-> anyedge==$past(edge_detected));
  a_output_eq_fn:assert property (state==OUTPUT
                                  |-> anyedge==$past(rise_mask(curr_in,prev_in)));
  a_output_only_updates: assert property (state!=OUTPUT |-> $stable(anyedge));

  // Backward consistency: OUTPUT must come from a detect event
  a_output_has_cause: assert property (state==OUTPUT
                                       |-> $past(state)==DETECT && $past(curr_in!=prev_in));

  // Coverage
  c_idle_detect_idle:      cover property (state==IDLE ##1 state==DETECT && (curr_in==prev_in) ##1 state==IDLE);
  c_rise_path:             cover property (state==IDLE ##1 state==DETECT && (rise_mask(curr_in,prev_in)!=0)
                                           ##1 state==OUTPUT ##1 state==IDLE);
  c_multi_bit_rise:        cover property (state==DETECT && $countones(rise_mask(curr_in,prev_in))>1 ##1 state==OUTPUT);
  c_fall_only_change:      cover property (state==DETECT && (curr_in!=prev_in) && (rise_mask(curr_in,prev_in)==0)
                                           ##1 state==OUTPUT && anyedge==8'h00);
  c_mixed_rise_fall:       cover property (state==DETECT && (rise_mask(curr_in,prev_in)!=0) && ((~curr_in)&prev_in)!=0
                                           ##1 state==OUTPUT);
endmodule

// Bind into DUT (accesses internals)
bind edge_detector edge_detector_sva #(.IDLE(IDLE), .DETECT(DETECT), .OUTPUT(OUTPUT))
  edge_detector_sva_i (
    .clk(clk),
    .in(in),
    .anyedge(anyedge),
    .state(state),
    .curr_in(curr_in),
    .prev_in(prev_in),
    .edge_detected(edge_detected)
  );