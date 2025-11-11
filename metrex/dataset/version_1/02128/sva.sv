// SVA for analinput
// Bind this file to the DUT. Focused, concise checks + coverage.

module analinput_sva #(parameter PADDLESIZE=0, SCREENHEIGHT=0)
(
  input  logic        clk,
  input  logic        sck,
  input  logic        miso,
  input  logic        mosi,
  input  logic        cs,
  input  logic [9:0]  pay,
  input  logic [9:0]  pby,
  input  logic [1:0]  state,
  input  logic [4:0]  sckcount,
  input  logic [11:0] datain,
  input  logic        ab
);
  // State encodings (match DUT)
  localparam int state0 = 0, state1 = 1, state2 = 2, state3 = 3;

  // Past-valid guards for posedge/negedge domains
  logic pv_p, pv_n;
  initial begin pv_p = 1'b0; pv_n = 1'b0; end
  always @(posedge clk)  pv_p <= 1'b1;
  always @(negedge clk)  pv_n <= 1'b1;

  // Copy of DUT function for exact result checks
  function automatic [9:0] paddlelimiter(input [9:0] py, input [3:0] paddlesize, input [9:0] screenheight);
    if (py < paddlesize/2) paddlelimiter = paddlesize/2;
    else if (py > screenheight-96/2) paddlelimiter = screenheight-paddlesize/2;
    else paddlelimiter = py;
  endfunction

  // sck mirrors clk
  assert property (@(posedge clk) sck == 1'b1);
  assert property (@(negedge clk) sck == 1'b0);

  // Legal state encoding
  assert property (@(posedge clk) state inside {state0,state1,state2,state3});

  // FSM sequencing and outputs
  assert property (@(posedge clk) disable iff(!pv_p)
    $past(state)==state0 |-> state==state1 && ab==1);

  assert property (@(posedge clk) disable iff(!pv_p)
    $past(state)==state1 |-> state==state2 && sckcount==5'd15 && cs==1'b0 && mosi==!$past(ab));

  assert property (@(posedge clk) disable iff(!pv_p)
    $past(state)==state2 && $past(sckcount)!=0 |-> state==state2 && sckcount==$past(sckcount)-1 && cs==1'b0 && $stable(mosi));

  assert property (@(posedge clk) disable iff(!pv_p)
    $past(state)==state2 && $past(sckcount)==0 |-> state==state3);

  assert property (@(posedge clk) disable iff(!pv_p)
    $past(state)==state3 |-> state==state1 && cs==1'b1 && mosi==1'b0);

  // ab updates only in state0/state1, stable otherwise; toggles in state1
  assert property (@(posedge clk) disable iff(!pv_p)
    $past(state) inside {state2,state3} |-> ab==$past(ab));
  assert property (@(posedge clk) disable iff(!pv_p)
    $past(state)==state1 |-> ab==!$past(ab));

  // datain behavior on negedge sck (clk)
  assert property (@(negedge clk) disable iff(!pv_n)
    state==state2 |=> datain == (($past(datain) << 1) | $past(miso)));
  assert property (@(negedge clk) disable iff(!pv_n)
    state==state1 |=> datain == 12'b0);

  // pay/pby update only in state3, correct source and exclusivity
  assert property (@(posedge clk) disable iff(!pv_p)
    $past(state)!=state3 |-> $stable(pay) && $stable(pby));

  assert property (@(posedge clk) disable iff(!pv_p)
    $past(state)==state3 && $past(ab)==1'b0 |-> pay==paddlelimiter(datain[7:0], PADDLESIZE[3:0], SCREENHEIGHT) && $stable(pby));

  assert property (@(posedge clk) disable iff(!pv_p)
    $past(state)==state3 && $past(ab)==1'b1 |-> pby==paddlelimiter(datain[10:8], PADDLESIZE[3:0], SCREENHEIGHT) && $stable(pay));

  // Output range sanity (independent of function internals)
  assert property (@(posedge clk) pay >= (PADDLESIZE/2) && pay <= (SCREENHEIGHT - PADDLESIZE/2));
  assert property (@(posedge clk) pby >= (PADDLESIZE/2) && pby <= (SCREENHEIGHT - PADDLESIZE/2));

  // cs/ mosi invariants by state
  assert property (@(posedge clk) state==state2 |-> cs==1'b0);
  assert property (@(posedge clk) state==state3 |-> cs==1'b1 && mosi==1'b0);

  // Coverage: full transfer and both ab branches
  cover property (@(posedge clk) pv_p && state==state1 ##1 (state==state2)[*16] ##1 state==state3 ##1 state==state1);
  cover property (@(posedge clk) pv_p && state==state3 && ab==1'b0);
  cover property (@(posedge clk) pv_p && state==state3 && ab==1'b1);
endmodule

// Bind to DUT
bind analinput analinput_sva #(.PADDLESIZE(PADDLESIZE), .SCREENHEIGHT(SCREENHEIGHT)) i_analinput_sva
(
  .clk(clk),
  .sck(sck),
  .miso(miso),
  .mosi(mosi),
  .cs(cs),
  .pay(pay),
  .pby(pby),
  .state(state),
  .sckcount(sckcount),
  .datain(datain),
  .ab(ab)
);