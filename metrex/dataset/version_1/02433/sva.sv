// SVA checker for exercise_8_10
module exercise_8_10_sva (
  input logic        Clk,
  input logic        x, y,
  input logic [1:0]  state
);

  default clocking cb @(posedge Clk); endclocking

  // Helpers
  let sp   = $past(state);
  let xyp  = $past({x,y});
  let past_known = !$isunknown({sp,xyp});

  // Next-state function matching DUT
  function automatic logic [1:0] ns (input logic [1:0] s, input logic x, y);
    unique case ({x,y})
      2'b00: ns = (s==2'b00) ? 2'b00 :
                  (s==2'b01) ? 2'b10 :
                  (s==2'b10) ? 2'b00 : 2'b10;
      2'b01: ns = (s==2'b00) ? 2'b00 :
                  (s==2'b01) ? 2'b11 :
                  (s==2'b10) ? 2'b00 : s;
      2'b10: ns = (s==2'b00) ? 2'b01 :
                  (s==2'b01) ? 2'b10 :
                  (s==2'b10) ? 2'b10 : 2'b00;
      default: // 2'b11
                  ns = (s==2'b00) ? 2'b01 :
                       (s==2'b01) ? 2'b11 :
                       (s==2'b10) ? 2'b11 : 2'b00;
    endcase
  endfunction

  // Initialization check
  initial begin
    assert (state === 2'b00)
      else $error("exercise_8_10: initial state must be 2'b00");
  end

  // Sanity: known inputs/state at sample points
  ap_inputs_known: assert property (!$isunknown({x,y}))
    else $error("exercise_8_10: x/y unknown at posedge");
  ap_state_known:  assert property (!$isunknown(state))
    else $error("exercise_8_10: state unknown at posedge");

  // State updates only on clock edges (no mid-cycle glitches)
  ap_sync_only: assert property (@(negedge Clk) $stable(state))
    else $error("exercise_8_10: state changed outside posedge");

  // Golden next-state check (1-cycle latency)
  ap_next: assert property (past_known |-> state == ns(sp, xyp[1], xyp[0]))
    else $error("exercise_8_10: next-state mismatch");

  // Functional coverage
  // - All states reachable
  cp_s0: cover property (state==2'b00);
  cp_s1: cover property (state==2'b01);
  cp_s2: cover property (state==2'b10);
  cp_s3: cover property (state==2'b11);

  // - All input combinations seen
  cp_i00: cover property ({x,y}==2'b00);
  cp_i01: cover property ({x,y}==2'b01);
  cp_i10: cover property ({x,y}==2'b10);
  cp_i11: cover property ({x,y}==2'b11);

  // - Exercise every (past state, past input) combination
  cp_c00_00: cover property (past_known && sp==2'b00 && xyp==2'b00);
  cp_c00_01: cover property (past_known && sp==2'b00 && xyp==2'b01);
  cp_c00_10: cover property (past_known && sp==2'b00 && xyp==2'b10);
  cp_c00_11: cover property (past_known && sp==2'b00 && xyp==2'b11);

  cp_c01_00: cover property (past_known && sp==2'b01 && xyp==2'b00);
  cp_c01_01: cover property (past_known && sp==2'b01 && xyp==2'b01);
  cp_c01_10: cover property (past_known && sp==2'b01 && xyp==2'b10);
  cp_c01_11: cover property (past_known && sp==2'b01 && xyp==2'b11);

  cp_c10_00: cover property (past_known && sp==2'b10 && xyp==2'b00);
  cp_c10_01: cover property (past_known && sp==2'b10 && xyp==2'b01);
  cp_c10_10: cover property (past_known && sp==2'b10 && xyp==2'b10);
  cp_c10_11: cover property (past_known && sp==2'b10 && xyp==2'b11);

  cp_c11_00: cover property (past_known && sp==2'b11 && xyp==2'b00);
  cp_c11_01: cover property (past_known && sp==2'b11 && xyp==2'b01);
  cp_c11_10: cover property (past_known && sp==2'b11 && xyp==2'b10);
  cp_c11_11: cover property (past_known && sp==2'b11 && xyp==2'b11);

endmodule

// Bind into DUT
bind exercise_8_10 exercise_8_10_sva exercise_8_10_sva_i (.*);