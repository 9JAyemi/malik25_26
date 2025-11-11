// SVA for PGM. Bind this file to the DUT.
// Usage example:
//   bind PGM PGM_sva #(.MAXH(MAXH)) u_PGM_sva (.*);

module PGM_sva #(
  parameter int MAXH = 10
)(
  input logic              CLK, RESET, IN_VALID, BUTTON,
  input logic [1:0]        MORE,
  input logic              OUT_VALID,
  input logic [1:0]        WIN,
  input logic [3:0]        CARD,
  input logic [3:0]        SUM,
  input logic [2:0]        state, next_state,
  input logic [3:0]        randcard,
  input integer            m_w,
  input logic              inIN, inBT,
  input logic [1:0]        inMR,
  input logic [4:0]        handA, handB
);

  // State encodings (mirror DUT)
  localparam ST_INIT   = 3'b000;
  localparam ST_FC     = 3'b001;
  localparam ST_SC     = 3'b010;
  localparam ST_A      = 3'b011;
  localparam ST_B      = 3'b100;
  localparam ST_WAIT   = 3'b101;
  localparam ST_OUTPUT = 3'b110;
  localparam ST_DONE   = 3'b111;

  default clocking cb @(posedge CLK); endclocking

  // ---------------- Core invariants ----------------

  // Reset effects (checked on cycle after RESET is 1)
  ap_reset_sync: assert property (RESET |=> (state==ST_INIT
                      && randcard==4'b0 && m_w==55332
                      && inIN==1'b0 && inBT==1'b0
                      && handA==5'd0 && handB==5'd0
                      && OUT_VALID==1'b0 && CARD==4'd0
                      && WIN==2'b10 && SUM==4'd0));

  // State always legal
  ap_state_legal: assert property (disable iff (RESET) (state inside {ST_INIT,ST_FC,ST_SC,ST_A,ST_B,ST_WAIT,ST_OUTPUT,ST_DONE}));

  // State register follows next_state
  ap_state_follows_next: assert property (disable iff (RESET)
    $past(!RESET) |-> state == $past(next_state));

  // next_state combinational decode
  ap_nst_init:  assert property (disable iff (RESET)
    (state==ST_INIT) |-> (next_state == ((inIN && inBT) ? ST_FC : ST_INIT)));

  ap_nst_fc:    assert property (disable iff (RESET)
    (state==ST_FC) |-> (next_state==ST_SC));

  ap_nst_sc:    assert property (disable iff (RESET)
    (state==ST_SC) |-> (next_state == ((handA>MAXH || handB>MAXH) ? ST_OUTPUT : ST_WAIT)));

  ap_nst_a:     assert property (disable iff (RESET)
    (state==ST_A) |-> (next_state == ((handA>MAXH || handB>MAXH) ? ST_OUTPUT : ST_WAIT)));

  ap_nst_b:     assert property (disable iff (RESET)
    (state==ST_B) |-> (next_state == ((handA>MAXH || handB>MAXH) ? ST_OUTPUT : ST_WAIT)));

  ap_nst_wait_hold: assert property (disable iff (RESET)
    (state==ST_WAIT && !(inIN && inBT)) |-> (next_state==ST_WAIT));

  ap_nst_wait_sel0: assert property (disable iff (RESET)
    (state==ST_WAIT && inIN && inBT && inMR==2'b00) |-> (next_state==ST_OUTPUT));
  ap_nst_wait_sel1: assert property (disable iff (RESET)
    (state==ST_WAIT && inIN && inBT && inMR==2'b01) |-> (next_state==ST_A));
  ap_nst_wait_sel2: assert property (disable iff (RESET)
    (state==ST_WAIT && inIN && inBT && inMR==2'b10) |-> (next_state==ST_B));
  ap_nst_wait_sel3: assert property (disable iff (RESET)
    (state==ST_WAIT && inIN && inBT && inMR==2'b11) |-> (next_state==ST_FC));

  // Input sampling registers
  ap_sample_inIN: assert property (disable iff (RESET) $past(!RESET) |-> inIN == $past(IN_VALID));
  ap_sample_inBT: assert property (disable iff (RESET) $past(!RESET) |-> inBT == $past(BUTTON));
  ap_sample_inMR: assert property (disable iff (RESET) $past(!RESET) |-> inMR == $past(MORE));

  // RNG/LFSR math and ranges
  ap_mw_update: assert property (disable iff (RESET)
    $past(!RESET) |-> m_w == 18000 * ($past(m_w) & 16'hFFFF) + ($past(m_w) >> 16));

  ap_randcard_func: assert property (disable iff (RESET)
    $past(!RESET) |-> randcard == (( $past(m_w) >> 4) % 8) + 1);

  ap_randcard_range: assert property (disable iff (RESET) randcard inside {[4'd1:4'd8]});

  // Hand updates
  ap_handA_init:  assert property (disable iff (RESET) (next_state==ST_INIT) |-> handA==5'd0);
  ap_handB_init:  assert property (disable iff (RESET) (next_state==ST_INIT) |-> handB==5'd0);

  ap_handA_hit:   assert property (disable iff (RESET)
    $past(!RESET) && (next_state inside {ST_FC,ST_A}) |-> handA == $past(handA) + $past(randcard));

  ap_handB_hit:   assert property (disable iff (RESET)
    $past(!RESET) && (next_state inside {ST_SC,ST_B}) |-> handB == $past(handB) + $past(randcard));

  ap_handA_hold:  assert property (disable iff (RESET)
    $past(!RESET) && (next_state inside {ST_SC,ST_B,ST_WAIT,ST_OUTPUT,ST_DONE}) |-> handA == $past(handA));

  ap_handB_hold:  assert property (disable iff (RESET)
    $past(!RESET) && (next_state inside {ST_FC,ST_A,ST_WAIT,ST_OUTPUT,ST_DONE}) |-> handB == $past(handB));

  // OUT_VALID and CARD behavior
  ap_outvalid_map: assert property (disable iff (RESET)
    (next_state inside {ST_FC,ST_A,ST_B,ST_OUTPUT}) ? (OUT_VALID==1'b1) : (OUT_VALID==1'b0));

  ap_card_deal: assert property (disable iff (RESET)
    $past(!RESET) && (next_state inside {ST_FC,ST_SC,ST_A,ST_B}) |-> CARD == $past(randcard));

  ap_card_zero_idle: assert property (disable iff (RESET)
    (next_state inside {ST_INIT,ST_WAIT,ST_DONE}) |-> CARD == 4'd0);

  ap_card_hold_output: assert property (disable iff (RESET)
    $past(!RESET) && next_state==ST_OUTPUT |-> CARD == $past(CARD));

  // WIN/SUM computation (based on previous hands, per nonblocking semantics)
  function automatic bit a_wins (logic [4:0] a, b);
    return ((a > b) || (b > MAXH)) && (a <= MAXH);
  endfunction
  function automatic bit b_wins (logic [4:0] a, b);
    return ((b > a) || (a > MAXH)) && (b <= MAXH);
  endfunction

  ap_winA: assert property (disable iff (RESET)
    $past(!RESET) && a_wins($past(handA), $past(handB)) |-> (WIN==2'b00 && SUM==$past(handA)));

  ap_winB: assert property (disable iff (RESET)
    $past(!RESET) && b_wins($past(handA), $past(handB)) |-> (WIN==2'b01 && SUM==$past(handB)));

  ap_draw: assert property (disable iff (RESET)
    $past(!RESET) && !(a_wins($past(handA),$past(handB)) || b_wins($past(handA),$past(handB))) |-> (WIN==2'b10 && SUM==4'd0));

  ap_win_code_legal: assert property (disable iff (RESET) WIN inside {2'b00,2'b01,2'b10});

  // ---------------- Useful coverage ----------------

  // Basic flow to first two cards
  cp_first_two: cover property (
    state==ST_INIT && inIN && inBT ##1 next_state==ST_FC ##1 state==ST_FC ##1 next_state==ST_SC);

  // WAIT decisions
  cp_wait_00: cover property (state==ST_WAIT && inIN && inBT && inMR==2'b00 ##1 next_state==ST_OUTPUT);
  cp_wait_01: cover property (state==ST_WAIT && inIN && inBT && inMR==2'b01 ##1 next_state==ST_A);
  cp_wait_10: cover property (state==ST_WAIT && inIN && inBT && inMR==2'b10 ##1 next_state==ST_B);
  cp_wait_11: cover property (state==ST_WAIT && inIN && inBT && inMR==2'b11 ##1 next_state==ST_FC);

  // Reach OUTPUT via bust
  cp_bustA: cover property ((state inside {ST_SC,ST_A,ST_B}) && handA>MAXH ##1 next_state==ST_OUTPUT);
  cp_bustB: cover property ((state inside {ST_SC,ST_A,ST_B}) && handB>MAXH ##1 next_state==ST_OUTPUT);

  // Winner outcomes
  cp_winA: cover property ($past(handA)>$past(handB) && $past(handA)<=MAXH ##1 WIN==2'b00);
  cp_winB: cover property ($past(handB)>$past(handA) && $past(handB)<=MAXH ##1 WIN==2'b01);
  cp_draw: cover property ($past(handA)==$past(handB) && $past(handA)<=MAXH ##1 WIN==2'b10);

  // Card extremes
  cp_card_min: cover property (randcard==4'd1);
  cp_card_max: cover property (randcard==4'd8);

endmodule