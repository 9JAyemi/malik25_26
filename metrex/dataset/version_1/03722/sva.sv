// SVA for pulse_generator
module pulse_generator_sva
(
  input  logic        clk,
  input  logic        reset,   // async active-high
  input  logic        in,
  input  logic        p,
  input  logic        l,
  input  logic [18:0] r,
  input  logic [1:0]  state
);
  localparam logic [1:0] IDLE=2'b00, COUNTING=2'b01, PULSE=2'b10;
  localparam int unsigned CNT_MAX = 19'd250000;

  default clocking cb @(posedge clk); endclocking

  // Basic sanity
  assert property (disable iff (reset) !$isunknown(state));
  assert property (disable iff (reset) state inside {IDLE, COUNTING, PULSE});
  assert property ($rose(reset) |=> (r==0 && l==0 && state==IDLE)); // p is intentionally not checked
  assert property (disable iff (reset) (state!=IDLE) |-> !$isunknown({p,l,r,state}));

  // IDLE behavior
  assert property (disable iff (reset) (state==IDLE && !in) |-> (l==0 && r==0));
  assert property (disable iff (reset) (state==IDLE && in) |=> (state==COUNTING && r==0 && l==1 && p==0));

  // COUNTING behavior
  assert property (disable iff (reset) (state==COUNTING) |-> (r<=CNT_MAX && l==1));
  assert property (disable iff (reset) (state==COUNTING && r<CNT_MAX) |=> (state==COUNTING && r==$past(r)+1 && p==0 && l==1));
  assert property (disable iff (reset) (state==COUNTING && r==CNT_MAX) |=> (state==PULSE && r==0 && p==1));

  // PULSE behavior
  assert property (disable iff (reset) (state==PULSE && !in) |-> (state==PULSE && r==0 && p==1 && l==0));
  assert property (disable iff (reset) (state==PULSE && in)  |=> (state==COUNTING && r==0 && p==0 && l==1));

  // Cross-checks
  assert property (disable iff (reset) p==1 |-> (state==PULSE || (state==COUNTING && r==CNT_MAX)));
  assert property (disable iff (reset) (state!=COUNTING) |-> (r==0));

  // Coverage
  cover property (disable iff (reset) (state==IDLE && in) ##1 (state==COUNTING && r==0));
  cover property (disable iff (reset) (state==COUNTING && r==CNT_MAX) ##1 (state==PULSE && p==1));
  cover property (disable iff (reset) (state==PULSE && !in) ##1 (state==PULSE && !in)); // hold in PULSE
  cover property (disable iff (reset) (state==PULSE && in) ##1 (state==COUNTING && r==0 && p==0));
  cover property (disable iff (reset) (state==COUNTING && r==0) ##[1:$] (state==COUNTING && r==CNT_MAX));
endmodule

// Bind into DUT (connects to internal regs r/state)
bind pulse_generator pulse_generator_sva
  u_pulse_generator_sva(
    .clk   (clk),
    .reset (reset),
    .in    (in),
    .p     (p),
    .l     (l),
    .r     (r),
    .state (state)
  );