// SVA for debounce_push_button
// Concise checks for state legality, transitions, counter behavior, and output updates.

module debounce_push_button_sva
  #(parameter IDLE = 2'b00, PRE_DEBOUNCE = 2'b01, DEBOUNCE = 2'b10)
  (
    input  logic        clk,
    input  logic        button,
    input  logic [1:0]  state,
    input  logic [1:0]  next_state, // not used directly, but exposed if needed
    input  logic [9:0]  debounce_counter,
    input  logic        debounced_button
  );

  default clocking cb @(posedge clk); endclocking
  default disable iff ($isunknown({state,next_state,debounce_counter,button,debounced_button}));

  // past_valid guard for $past usage
  bit past_valid;
  always_ff @(posedge clk) past_valid <= 1'b1;

  // State legality
  a_state_legal:      assert property (state      inside {IDLE, PRE_DEBOUNCE, DEBOUNCE});
  a_next_state_legal: assert property (next_state inside {IDLE, PRE_DEBOUNCE, DEBOUNCE});

  // IDLE transitions
  a_idle_stay_0: assert property (state==IDLE && !button |=> state==IDLE);
  a_idle_to_pre: assert property (state==IDLE &&  button |=> state==PRE_DEBOUNCE);

  // PRE_DEBOUNCE behavior
  a_pre_hold:    assert property (state==PRE_DEBOUNCE &&  button |=> state==PRE_DEBOUNCE && $stable(debounce_counter));
  a_pre_to_deb:  assert property (state==PRE_DEBOUNCE && !button |=> state==DEBOUNCE && debounce_counter==0);

  // DEBOUNCE behavior: continue counting while button=1 and counter<9
  a_deb_count:   assert property (state==DEBOUNCE && button && (debounce_counter<10'd9)
                                  |=> state==DEBOUNCE
                                  && debounce_counter==$past(debounce_counter)+1
                                  && $stable(debounced_button));

  // DEBOUNCE exit: on !button or counter>=9, commit output and go IDLE
  a_deb_exit:    assert property (state==DEBOUNCE && (!button || debounce_counter>=10'd9)
                                  |=> state==IDLE && debounced_button==$past(button));

  // Output may only change on DEBOUNCE exit cycle
  a_db_change_only_on_exit:
    assert property (past_valid && (debounced_button != $past(debounced_button))
                     |-> $past(state)==DEBOUNCE
                         && !($past(button) && ($past(debounce_counter)<10'd9)));

  // Coverage
  c_idle_stay:     cover property (state==IDLE && !button ##1 state==IDLE);
  c_idle_to_pre:   cover property (state==IDLE &&  button ##1 state==PRE_DEBOUNCE);
  c_pre_to_deb:    cover property (state==PRE_DEBOUNCE && !button ##1 state==DEBOUNCE && debounce_counter==0);
  c_deb_early0:    cover property (state==DEBOUNCE && !button ##1 state==IDLE && debounced_button==0);
  c_deb_count9_to1: cover property (
                      state==DEBOUNCE && debounce_counter==0 && button
                      ##1 (state==DEBOUNCE && button && debounce_counter<10'd9)[*8]
                      ##1 state==DEBOUNCE && button && debounce_counter==10'd9
                      ##1 state==IDLE && debounced_button==1
                    );

endmodule

// Bind into the DUT
bind debounce_push_button debounce_push_button_sva
  #(.IDLE(IDLE), .PRE_DEBOUNCE(PRE_DEBOUNCE), .DEBOUNCE(DEBOUNCE))
  u_debounce_push_button_sva (
    .clk(clk),
    .button(button),
    .state(state),
    .next_state(next_state),
    .debounce_counter(debounce_counter),
    .debounced_button(debounced_button)
  );