// SVA for WhacAMole
// Bind-friendly: uses wildcard bind (.*) to connect to DUT internals

module WhacAMole_sva (
  input logic              clk_1us,
  input logic              reset,
  input logic              PRESS_VALID,
  input logic              timesup,
  input logic [3:0]        random,
  input logic [3:0]        mallet_position,
  input logic [3:0]        BCD0,
  input logic [3:0]        BCD1,
  input logic [4:0]        mole_position,
  input logic [4:0]        next_mole,
  input logic [1:0]        state,
  input logic [1:0]        next_state,
  input logic [19:0]       counter500000,
  input logic [19:0]       next_counter500000,
  input logic              generatenewmole,
  input logic              next_generatenewmole,
  input logic              hit
);

  localparam logic [1:0] status0 = 2'h0;
  localparam logic [1:0] status1 = 2'h1;
  localparam logic [1:0] status2 = 2'h2;

  default clocking cb @(posedge clk_1us); endclocking
  default disable iff (!reset)

  // Reset values (checked during reset)
  assert property (@(posedge clk_1us) !reset |-> (mole_position==5'd0 && state==status0 &&
                                                  BCD0==4'd0 && BCD1==4'd0 &&
                                                  counter500000==20'd0 && generatenewmole==1'b0));

  // Registered <= next_* relation (only when reset was deasserted for at least 1 cycle)
  assert property (reset && $past(reset) |-> (
                     mole_position      == $past(next_mole)            &&
                     state              == $past(next_state)           &&
                     BCD0               == $past(next_BCD0)            &&
                     BCD1               == $past(next_BCD1)            &&
                     counter500000      == $past(next_counter500000)   &&
                     generatenewmole    == $past(next_generatenewmole)));

  // State encoding and counter range
  assert property (state inside {status0,status1,status2});
  assert property (counter500000 <= 20'd500000);

  // Hit combinational definition (exactly)
  assert property (hit == ((mallet_position == mole_position[3:0]) && !timesup && PRESS_VALID));

  // BCD scoring behavior
  assert property (reset && $past(reset) && !hit |=> (BCD0==$past(BCD0) && BCD1==$past(BCD1)));
  assert property (reset && $past(reset) && hit && (BCD0!=4'd9) |=> (BCD0==$past(BCD0)+4'd1 && BCD1==$past(BCD1)));
  assert property (reset && $past(reset) && hit && (BCD0==4'd9) |=> (BCD0==4'd0 && BCD1==$past(BCD1)+4'd1));

  // State 0 transitions
  assert property (state==status0 && hit                      |=> (state==status2 && counter500000==20'd0));
  assert property (state==status0 && !hit && counter500000==20'd500000 |=> (state==status1 && counter500000==20'd0));
  assert property (state==status0 && !hit && counter500000!=20'd500000 |=> (state==status0 && counter500000==$past(counter500000)+20'd1));

  // State 1 transitions
  assert property (state==status1 && hit                      |=> (state==status2 && counter500000==20'd0));
  assert property (state==status1 && !hit && counter500000==20'd500000 |=> (state==status2 && counter500000==20'd0));
  assert property (state==status1 && !hit && counter500000!=20'd500000 |=> (state==status1 && counter500000==$past(counter500000)+20'd1));

  // State 2 transitions + generateNewMole pulse
  assert property (state==status2 && counter500000==20'd500000 |=> (state==status0 && counter500000==20'd0 && generatenewmole));
  assert property (state==status2 && counter500000!=20'd500000 |=> (state==status2 && counter500000==$past(counter500000)+20'd1 && !generatenewmole));
  assert property (generatenewmole |-> ($past(state)==status2 && $past(counter500000)==20'd500000));
  assert property (generatenewmole |=> !generatenewmole); // one-cycle pulse

  // Mole update semantics
  assert property (hit |=> mole_position == 5'b10000);
  assert property (state==status2 |=> mole_position == 5'b10000);
  assert property (generatenewmole && !timesup |=> (mole_position[4]==1'b0 && mole_position[3:0]==$past(random)));
  assert property (!hit && state!=status2 && !(generatenewmole && !timesup) |=> mole_position==$past(mole_position));

  // No new mole when timesup blocks generation
  assert property (generatenewmole && timesup |=> mole_position==$past(mole_position));

  // Encoding: hidden mole is exactly 5'b10000
  assert property (mole_position[4] |-> mole_position[3:0]==4'd0);

  // No illegal direct transitions
  assert property ($rose(state==status2) && $past(state)==status0 |-> $past(hit));
  assert property ($rose(state==status2) && $past(state)==status1 |-> ($past(hit) || $past(counter500000==20'd500000)));
  assert property ($rose(state==status0) && $past(state)==status2 |-> $past(counter500000==20'd500000));

  // Functional covers
  cover property (state==status0 ##1 state==status1 ##1 state==status2 ##1 state==status0);
  cover property (hit && (BCD0==4'd9));                // wrap BCD0 -> increment BCD1
  cover property (generatenewmole && !timesup);        // new mole generation opportunity
  cover property (mole_position==5'b10000);            // hidden mole observed
  cover property (PRESS_VALID && (mallet_position==mole_position[3:0]) && timesup && !hit); // timesup gates hit
  cover property (state==status1 && hit);              // hit in state1 path

endmodule

// Bind into DUT
bind WhacAMole WhacAMole_sva sva_i (.*);