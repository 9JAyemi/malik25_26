// SVA for chatgpt_generate_edge_detect
// Bind-friendly checker; concise but covers state/output mapping, transitions, and coverage.

module edge_detect_sva
  #(parameter IDLE = 2'b00,
              RISE_DETECT = 2'b01,
              FALL_DETECT = 2'b10)
(
  input  logic        clk,
  input  logic        rst_n,
  input  logic        a,
  input  logic        select,
  input  logic        rise,
  input  logic        fall,
  input  logic [1:0]  state,
  input  logic [1:0]  next_state,
  input  logic        active_edge
);

  default clocking cb @(posedge clk); endclocking
  default disable iff (!rst_n);

  // Known/valid checks
  ap_known:        assert property (!$isunknown({state,next_state,rise,fall,active_edge})); 
  ap_legal_state:  assert property (state inside {IDLE, RISE_DETECT, FALL_DETECT});

  // Reset behavior (checked on clock)
  ap_reset:        assert property (!rst_n |-> (state==IDLE && rise==0 && fall==0 && active_edge==0));

  // Output mapping (same-cycle mapping to state)
  ap_idle_outs:    assert property (state==IDLE        |-> (rise==0 && fall==0 && active_edge==0));
  ap_rise_outs:    assert property (state==RISE_DETECT |-> (rise==1 && fall==0 && active_edge==1));
  ap_fall_outs:    assert property (state==FALL_DETECT |-> (rise==0 && fall==1 && active_edge==0));

  // Onehot0 on outputs
  ap_onehot0:      assert property (!(rise && fall));

  // Combinational next_state correctness
  logic [1:0] exp_ns;
  always_comb begin
    unique case (state)
      IDLE:         exp_ns = select ? (a ? RISE_DETECT : FALL_DETECT) : IDLE;
      RISE_DETECT:  exp_ns = a ? RISE_DETECT : IDLE;
      FALL_DETECT:  exp_ns = a ? IDLE : FALL_DETECT;
      default:      exp_ns = IDLE;
    endcase
    if (!$isunknown({state,a,select,next_state}))
      assert (next_state == exp_ns)
        else $error("next_state mismatch exp=%0b got=%0b (state=%0b sel=%0b a=%0b)",
                    exp_ns, next_state, state, select, a);
  end

  // Sequential: state loads previous next_state
  ap_state_follows_ns: assert property (($past(rst_n)) |-> (state == $past(next_state)));

  // No cross transitions between detect states
  ap_no_rise_to_fall:  assert property (state==RISE_DETECT |=> state != FALL_DETECT);
  ap_no_fall_to_rise:  assert property (state==FALL_DETECT |=> state != RISE_DETECT);

  // Entering detect states must be legal
  ap_enter_rise:       assert property ($rose(state==RISE_DETECT) |-> $past(state==IDLE && select && a));
  ap_enter_fall:       assert property ($rose(state==FALL_DETECT) |-> $past(state==IDLE && select && !a));

  // Coverage
  cv_all_states: cover property (state==IDLE ##1 state==RISE_DETECT ##[1:$] state==IDLE
                                            ##1 state==FALL_DETECT ##[1:$] state==IDLE);
  cv_hold_rise:  cover property (state==RISE_DETECT ##1 state==RISE_DETECT);
  cv_hold_fall:  cover property (state==FALL_DETECT ##1 state==FALL_DETECT);
  cv_entry_rise: cover property (state==IDLE && select && a ##1 state==RISE_DETECT);
  cv_entry_fall: cover property (state==IDLE && select && !a ##1 state==FALL_DETECT);

endmodule

// Bind into the DUT (tools typically allow binding to internal regs)
bind chatgpt_generate_edge_detect edge_detect_sva
  #(.IDLE(IDLE), .RISE_DETECT(RISE_DETECT), .FALL_DETECT(FALL_DETECT))
  u_edge_detect_sva (.*);