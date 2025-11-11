// SVA for gfx_transform
// Drop inside the module (or bind this block) with the same scope as signals.
// Assumes posedge clk_i, async active-high rst_i.

`ifndef GFX_TRANSFORM_SVA
`define GFX_TRANSFORM_SVA

// Default clocking and reset gating
default clocking gfx_cb @(posedge clk_i); endclocking
default disable iff (rst_i);

// ------------------------- Reset behavior -------------------------
assert property (@(posedge clk_i) rst_i |-> (state==wait_state && ack_o==0
  && p0_x_o==0 && p0_y_o==0 && p0_z_o==0
  && p1_x_o==0 && p1_y_o==0 && p1_z_o==0
  && p2_x_o==0 && p2_y_o==0 && p2_z_o==0))
  else $error("Reset did not clear state/outputs");

// ------------------------- FSM correctness -------------------------
assert property (state==wait_state && transform_i |=> state==transform_state)
  else $error("FSM: transform_i in wait_state must go to transform_state");

assert property (state==wait_state && !transform_i && forward_i |=> state==forward_state)
  else $error("FSM: forward_i (no transform_i) in wait_state must go to forward_state");

// One-cycle pulse states
assert property (state==forward_state |=> state==wait_state)
  else $error("FSM: forward_state must return to wait_state next cycle");

assert property (state==transform_state |=> state==wait_state)
  else $error("FSM: transform_state must return to wait_state next cycle");

// Only legal states
assert property (!(state===2'b11))
  else $error("FSM: illegal state 2'b11");

// Enter non-wait only from wait
assert property ((state==forward_state || state==transform_state) |-> $past(state)==wait_state)
  else $error("FSM: non-wait state entered from non-wait");

// Priority when both asserted
assert property (state==wait_state && transform_i && forward_i |=> state==transform_state)
  else $error("FSM: transform_i must take priority over forward_i");

// ------------------------- Ack protocol -------------------------
assert property (ack_o == (state!=wait_state))
  else $error("ACK must reflect non-wait state");

assert property (ack_o |=> !ack_o)
  else $error("ACK must be a single-cycle pulse");

// ------------------------- Forward path functional -------------------------
property p_forward_id0;
  state==wait_state && !transform_i && forward_i && point_id_i==2'b00 |=> 
    (p0_x_o==$past(x_i) && p0_y_o==$past(y_i) && p0_z_o==$past(z_i[point_width-1:0]))
    && $stable(p1_x_o) && $stable(p1_y_o) && $stable(p1_z_o)
    && $stable(p2_x_o) && $stable(p2_y_o) && $stable(p2_z_o);
endproperty
assert property (p_forward_id0) else $error("Forward path (id 0) mismatch");

property p_forward_id1;
  state==wait_state && !transform_i && forward_i && point_id_i==2'b01 |=> 
    (p1_x_o==$past(x_i) && p1_y_o==$past(y_i) && p1_z_o==$past(z_i[point_width-1:0]))
    && $stable(p0_x_o) && $stable(p0_y_o) && $stable(p0_z_o)
    && $stable(p2_x_o) && $stable(p2_y_o) && $stable(p2_z_o);
endproperty
assert property (p_forward_id1) else $error("Forward path (id 1) mismatch");

property p_forward_id2;
  state==wait_state && !transform_i && forward_i && point_id_i==2'b10 |=> 
    (p2_x_o==$past(x_i) && p2_y_o==$past(y_i) && p2_z_o==$past(z_i[point_width-1:0]))
    && $stable(p0_x_o) && $stable(p0_y_o) && $stable(p0_z_o)
    && $stable(p1_x_o) && $stable(p1_y_o) && $stable(p1_z_o);
endproperty
assert property (p_forward_id2) else $error("Forward path (id 2) mismatch");

// ------------------------- Transform capture and apply -------------------------
// Multiplies captured on transform command
assert property (state==wait_state && transform_i |=> 
  aax==$past(aa)*$past(x_i) && aby==$past(ab)*$past(y_i) && acz==$past(ac)*$past(z_i) &&
  bax==$past(ba)*$past(x_i) && bby==$past(bb)*$past(y_i) && bcz==$past(bc)*$past(z_i) &&
  cax==$past(ca)*$past(x_i) && cby==$past(cb)*$past(y_i) && ccz==$past(cc)*$past(z_i))
  else $error("Transform products not captured correctly");

// Outputs updated with truncated transform results, selected by current point_id_i
property p_transform_id0;
  state==transform_state && point_id_i==2'b00 |-> 
    (p0_x_o==x_prime_trunc && p0_y_o==y_prime_trunc && p0_z_o==z_prime_trunc[point_width-1:0])
    && $stable(p1_x_o) && $stable(p1_y_o) && $stable(p1_z_o)
    && $stable(p2_x_o) && $stable(p2_y_o) && $stable(p2_z_o);
endproperty
assert property (p_transform_id0) else $error("Transform path (id 0) mismatch");

property p_transform_id1;
  state==transform_state && point_id_i==2'b01 |-> 
    (p1_x_o==x_prime_trunc && p1_y_o==y_prime_trunc && p1_z_o==z_prime_trunc[point_width-1:0])
    && $stable(p0_x_o) && $stable(p0_y_o) && $stable(p0_z_o)
    && $stable(p2_x_o) && $stable(p2_y_o) && $stable(p2_z_o);
endproperty
assert property (p_transform_id1) else $error("Transform path (id 1) mismatch");

property p_transform_id2;
  state==transform_state && point_id_i==2'b10 |-> 
    (p2_x_o==x_prime_trunc && p2_y_o==y_prime_trunc && p2_z_o==z_prime_trunc[point_width-1:0])
    && $stable(p0_x_o) && $stable(p0_y_o) && $stable(p0_z_o)
    && $stable(p1_x_o) && $stable(p1_y_o) && $stable(p1_z_o);
endproperty
assert property (p_transform_id2) else $error("Transform path (id 2) mismatch");

// ------------------------- Sanity: no X on key outputs/states (post-reset) -------------------------
assert property (!$isunknown({state,ack_o,
  p0_x_o,p0_y_o,p0_z_o,p1_x_o,p1_y_o,p1_z_o,p2_x_o,p2_y_o,p2_z_o}))
  else $error("Unknown (X/Z) detected on state/outputs");

// ------------------------- Coverage -------------------------
cover property (state==wait_state && forward_i && !transform_i && point_id_i==2'b00 |=> state==forward_state ##1 state==wait_state);
cover property (state==wait_state && forward_i && !transform_i && point_id_i==2'b01 |=> state==forward_state ##1 state==wait_state);
cover property (state==wait_state && forward_i && !transform_i && point_id_i==2'b10 |=> state==forward_state ##1 state==wait_state);

cover property (state==wait_state && transform_i && point_id_i==2'b00 |=> state==transform_state ##1 state==wait_state);
cover property (state==wait_state && transform_i && point_id_i==2'b01 |=> state==transform_state ##1 state==wait_state);
cover property (state==wait_state && transform_i && point_id_i==2'b10 |=> state==transform_state ##1 state==wait_state);

cover property (state==wait_state && transform_i && forward_i |=> state==transform_state);

`endif // GFX_TRANSFORM_SVA