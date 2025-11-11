// SVA for moore_machine
// Bind inside DUT to access internal state

module moore_machine_sva (
  input  logic        clk,
  input  logic        reset,
  input  logic        x,
  input  logic        y,
  input  logic [1:0]  z,
  input  logic [1:0]  state
);
  // Mirror DUT encoding
  localparam logic [1:0] A = 2'b00;
  localparam logic [1:0] B = 2'b01;
  localparam logic [1:0] C = 2'b10;

  // Basic sanity
  ap_state_legal_clk:  assert property (@(posedge clk)   state inside {A,B,C});
  ap_state_legal_rst:  assert property (@(posedge reset) ##0 state inside {A,B,C});
  ap_no_x_state_z:     assert property (@(posedge clk or posedge reset) !$isunknown(state) && !$isunknown(z));

  // Asynchronous reset behavior
  ap_rst_immediate_A:  assert property (@(posedge reset) ##0 (state == A));
  ap_rst_holds_A:      assert property (@(posedge clk or posedge reset) reset |-> state == A);

  // Moore output mapping (z must match state whenever state can change)
  ap_z_matches_state:  assert property (@(posedge clk or posedge reset)
                                        ##0 (((state==A) && (z==2'b00)) ||
                                             ((state==B) && (z==2'b01)) ||
                                             ((state==C) && (z==2'b10))));

  // Next-state function (disable around any reset activity)
  // From A
  ap_A_to_B: assert property (@(posedge clk)
                  disable iff (reset || $past(reset))
                  ($past(state)==A &&  $past(x) && !$past(y)) |=> state==B);
  ap_A_to_C: assert property (@(posedge clk)
                  disable iff (reset || $past(reset))
                  ($past(state)==A &&  $past(x) &&  $past(y)) |=> state==C);
  ap_A_to_A: assert property (@(posedge clk)
                  disable iff (reset || $past(reset))
                  ($past(state)==A && (!($past(x) && !$past(y)) && !($past(x) && $past(y)))) |=> state==A);

  // From B
  ap_B_to_B: assert property (@(posedge clk)
                  disable iff (reset || $past(reset))
                  ($past(state)==B &&  $past(x)) |=> state==B);
  ap_B_to_A: assert property (@(posedge clk)
                  disable iff (reset || $past(reset))
                  ($past(state)==B && !$past(x)) |=> state==A);

  // From C
  ap_C_to_C: assert property (@(posedge clk)
                  disable iff (reset || $past(reset))
                  ($past(state)==C &&  $past(x)) |=> state==C);
  ap_C_to_A: assert property (@(posedge clk)
                  disable iff (reset || $past(reset))
                  ($past(state)==C && !$past(x)) |=> state==A);

  // Coverage: states and all transitions (including input-qualified ones)
  cv_state_A: cover property (@(posedge clk) state==A);
  cv_state_B: cover property (@(posedge clk) state==B);
  cv_state_C: cover property (@(posedge clk) state==C);

  cv_A_to_B:  cover property (@(posedge clk)
                    disable iff (reset || $past(reset))
                    ($past(state)==A &&  $past(x) && !$past(y) && state==B));
  cv_A_to_C:  cover property (@(posedge clk)
                    disable iff (reset || $past(reset))
                    ($past(state)==A &&  $past(x) &&  $past(y) && state==C));
  cv_A_to_A:  cover property (@(posedge clk)
                    disable iff (reset || $past(reset))
                    ($past(state)==A && (!($past(x) && !$past(y)) && !($past(x) && $past(y))) && state==A));
  cv_B_to_B:  cover property (@(posedge clk)
                    disable iff (reset || $past(reset))
                    ($past(state)==B &&  $past(x) && state==B));
  cv_B_to_A:  cover property (@(posedge clk)
                    disable iff (reset || $past(reset))
                    ($past(state)==B && !$past(x) && state==A));
  cv_C_to_C:  cover property (@(posedge clk)
                    disable iff (reset || $past(reset))
                    ($past(state)==C &&  $past(x) && state==C));
  cv_C_to_A:  cover property (@(posedge clk)
                    disable iff (reset || $past(reset))
                    ($past(state)==C && !$past(x) && state==A));

  cv_reset:   cover property (@(posedge reset) ##0 state==A);
endmodule

// Bind into DUT
bind moore_machine moore_machine_sva sva(
  .clk   (clk),
  .reset (reset),
  .x     (x),
  .y     (y),
  .z     (z),
  .state (state)
);