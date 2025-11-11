// SVA for FSM
// Bind this file to the DUT: bind FSM FSM_sva #(.n(n), .k(k), .l(l), .m(m)) u_fsm_sva();

module FSM_sva #(parameter int n=8, k=3, l=2, m=2) ();

  // Access DUT signals hierarchically through bind
  // clk, reset, in, out, state, compressed_state are in DUT scope

  // State encodings (match DUT)
  localparam [k-1:0] STATE_A = 3'b000;
  localparam [k-1:0] STATE_B = 3'b001;
  localparam [k-1:0] STATE_C = 3'b010;
  localparam [k-1:0] STATE_D = 3'b011;
  localparam [k-1:0] STATE_E = 3'b100;
  localparam [k-1:0] STATE_F = 3'b101;
  localparam [k-1:0] STATE_G = 3'b110;
  localparam [k-1:0] STATE_H = 3'b111;

  function automatic [l-1:0] comp_of_state (input [k-1:0] s);
    case (s)
      STATE_A, STATE_E: comp_of_state = 2'b00;
      STATE_B, STATE_F: comp_of_state = 2'b01;
      STATE_C, STATE_G: comp_of_state = 2'b10;
      STATE_D, STATE_H: comp_of_state = 2'b11;
      default:          comp_of_state = 'x;
    endcase
  endfunction

  function automatic [k-1:0] next_state_fn (input [k-1:0] s, input bit b);
    case (s)
      STATE_A: next_state_fn = b ? STATE_B : STATE_C;
      STATE_B: next_state_fn = b ? STATE_D : STATE_C;
      STATE_C: next_state_fn = b ? STATE_D : STATE_E;
      STATE_D: next_state_fn = b ? STATE_F : STATE_E;
      STATE_E: next_state_fn = b ? STATE_F : STATE_G;
      STATE_F: next_state_fn = b ? STATE_H : STATE_G;
      STATE_G: next_state_fn = b ? STATE_H : STATE_A;
      STATE_H: next_state_fn = b ? STATE_B : STATE_A;
      default: next_state_fn = 'x;
    endcase
  endfunction

  default clocking cb @(posedge clk); endclocking

  // Sanity/legality
  a_no_x:            assert property ( !$isunknown({state, compressed_state, out}) );
  a_state_legal:     assert property ( state inside {STATE_A,STATE_B,STATE_C,STATE_D,STATE_E,STATE_F,STATE_G,STATE_H} );
  a_in_valid:        assert property ( disable iff (reset) (in == '0) || (in == 'd1) );
  a_out_eq_comp:     assert property ( out == compressed_state );

  // Reset behavior
  a_reset:           assert property ( reset |=> (state == STATE_A && compressed_state == 2'b00) );

  // Compressed state must match current state cluster
  a_comp_mapping:    assert property ( disable iff (reset) compressed_state == comp_of_state(state) );

  // Deterministic next state and compressed encoding from previous inputs
  a_next_and_comp:   assert property ( $past(!reset) && ($past(in) == '0 || $past(in) == 'd1)
                                       |-> state == next_state_fn($past(state), ($past(in) == 'd1))
                                           && compressed_state == comp_of_state(state) );

  // Transition assertions per state/input (redundant with a_next_and_comp, but precise diagnostics)
  a_A_0: assert property ( disable iff (reset) $past(state)==STATE_A && $past(in)=='0 |-> state==STATE_C && compressed_state==2'b10 );
  a_A_1: assert property ( disable iff (reset) $past(state)==STATE_A && $past(in)=='d1 |-> state==STATE_B && compressed_state==2'b01 );

  a_B_0: assert property ( disable iff (reset) $past(state)==STATE_B && $past(in)=='0 |-> state==STATE_C && compressed_state==2'b10 );
  a_B_1: assert property ( disable iff (reset) $past(state)==STATE_B && $past(in)=='d1 |-> state==STATE_D && compressed_state==2'b11 );

  a_C_0: assert property ( disable iff (reset) $past(state)==STATE_C && $past(in)=='0 |-> state==STATE_E && compressed_state==2'b00 );
  a_C_1: assert property ( disable iff (reset) $past(state)==STATE_C && $past(in)=='d1 |-> state==STATE_D && compressed_state==2'b11 );

  a_D_0: assert property ( disable iff (reset) $past(state)==STATE_D && $past(in)=='0 |-> state==STATE_E && compressed_state==2'b00 );
  a_D_1: assert property ( disable iff (reset) $past(state)==STATE_D && $past(in)=='d1 |-> state==STATE_F && compressed_state==2'b01 );

  a_E_0: assert property ( disable iff (reset) $past(state)==STATE_E && $past(in)=='0 |-> state==STATE_G && compressed_state==2'b10 );
  a_E_1: assert property ( disable iff (reset) $past(state)==STATE_E && $past(in)=='d1 |-> state==STATE_F && compressed_state==2'b01 );

  a_F_0: assert property ( disable iff (reset) $past(state)==STATE_F && $past(in)=='0 |-> state==STATE_G && compressed_state==2'b10 );
  a_F_1: assert property ( disable iff (reset) $past(state)==STATE_F && $past(in)=='d1 |-> state==STATE_H && compressed_state==2'b11 );

  a_G_0: assert property ( disable iff (reset) $past(state)==STATE_G && $past(in)=='0 |-> state==STATE_A && compressed_state==2'b00 );
  a_G_1: assert property ( disable iff (reset) $past(state)==STATE_G && $past(in)=='d1 |-> state==STATE_H && compressed_state==2'b11 );

  a_H_0: assert property ( disable iff (reset) $past(state)==STATE_H && $past(in)=='0 |-> state==STATE_A && compressed_state==2'b00 );
  a_H_1: assert property ( disable iff (reset) $past(state)==STATE_H && $past(in)=='d1 |-> state==STATE_B && compressed_state==2'b01 );

  // Coverage: reachability of all states and compressed encodings
  c_reset:    cover property ( reset ##1 state==STATE_A && compressed_state==2'b00 );
  c_states:   cover property ( !reset && state==STATE_A );
  c_stateb:   cover property ( !reset && state==STATE_B );
  c_statec:   cover property ( !reset && state==STATE_C );
  c_stated:   cover property ( !reset && state==STATE_D );
  c_statee:   cover property ( !reset && state==STATE_E );
  c_statef:   cover property ( !reset && state==STATE_F );
  c_stateg:   cover property ( !reset && state==STATE_G );
  c_stateh:   cover property ( !reset && state==STATE_H );
  c_comp00:   cover property ( !reset && compressed_state==2'b00 );
  c_comp01:   cover property ( !reset && compressed_state==2'b01 );
  c_comp10:   cover property ( !reset && compressed_state==2'b10 );
  c_comp11:   cover property ( !reset && compressed_state==2'b11 );

  // Coverage: all 16 directed transitions (state,input)
  c_A0: cover property ( $past(!reset) && $past(state)==STATE_A && $past(in)=='0 ##1 state==STATE_C );
  c_A1: cover property ( $past(!reset) && $past(state)==STATE_A && $past(in)=='d1 ##1 state==STATE_B );
  c_B0: cover property ( $past(!reset) && $past(state)==STATE_B && $past(in)=='0 ##1 state==STATE_C );
  c_B1: cover property ( $past(!reset) && $past(state)==STATE_B && $past(in)=='d1 ##1 state==STATE_D );
  c_C0: cover property ( $past(!reset) && $past(state)==STATE_C && $past(in)=='0 ##1 state==STATE_E );
  c_C1: cover property ( $past(!reset) && $past(state)==STATE_C && $past(in)=='d1 ##1 state==STATE_D );
  c_D0: cover property ( $past(!reset) && $past(state)==STATE_D && $past(in)=='0 ##1 state==STATE_E );
  c_D1: cover property ( $past(!reset) && $past(state)==STATE_D && $past(in)=='d1 ##1 state==STATE_F );
  c_E0: cover property ( $past(!reset) && $past(state)==STATE_E && $past(in)=='0 ##1 state==STATE_G );
  c_E1: cover property ( $past(!reset) && $past(state)==STATE_E && $past(in)=='d1 ##1 state==STATE_F );
  c_F0: cover property ( $past(!reset) && $past(state)==STATE_F && $past(in)=='0 ##1 state==STATE_G );
  c_F1: cover property ( $past(!reset) && $past(state)==STATE_F && $past(in)=='d1 ##1 state==STATE_H );
  c_G0: cover property ( $past(!reset) && $past(state)==STATE_G && $past(in)=='0 ##1 state==STATE_A );
  c_G1: cover property ( $past(!reset) && $past(state)==STATE_G && $past(in)=='d1 ##1 state==STATE_H );
  c_H0: cover property ( $past(!reset) && $past(state)==STATE_H && $past(in)=='0 ##1 state==STATE_A );
  c_H1: cover property ( $past(!reset) && $past(state)==STATE_H && $past(in)=='d1 ##1 state==STATE_B );

endmodule

// Bind example:
// bind FSM FSM_sva #(.n(n), .k(k), .l(l), .m(m)) u_fsm_sva();