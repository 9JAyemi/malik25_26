// SVA for db_controller
// Bind into the DUT to check behavior and cover key scenarios

module db_controller_sva #(
  parameter IDLE  = 3'b000, LOAD  = 3'b001, YVER = 3'b011, YHOR = 3'b010,
            CVER  = 3'b110, CHOR  = 3'b111, OUTLT= 3'b101, OUT  = 3'b100
)(
  input  logic        clk,
  input  logic        rst_n,
  input  logic        start_i,
  input  logic        done_o,
  input  logic [8:0]  cnt_r,
  input  logic [2:0]  state,
  input  logic [2:0]  next,
  input  logic [8:0]  cycles,
  input  logic        isluma,
  input  logic        isver
);

  default clocking cb @ (posedge clk); endclocking
  default disable iff (!rst_n)

  // cycles decode must match state
  assert property (state==LOAD  |-> cycles==9'd384);
  assert property (state==YVER  |-> cycles==9'd132);
  assert property (state==YHOR  |-> cycles==9'd140);
  assert property (state==CVER  |-> cycles==9'd68 );
  assert property (state==CHOR  |-> cycles==9'd76 );
  assert property (state==OUTLT |-> cycles==9'd67 );
  assert property (state==OUT   |-> cycles==9'd384);
  assert property (state==IDLE  |-> cycles==9'd0  );

  // allowed transitions (state machine)
  assert property (state==IDLE &&  start_i    |=> state==LOAD);
  assert property (state==IDLE && !start_i    |=> state==IDLE);

  assert property (state==LOAD  && cnt_r!=cycles |=> state==LOAD);
  assert property (state==LOAD  && cnt_r==cycles |=> state==YVER);

  assert property (state==YVER  && cnt_r!=cycles |=> state==YVER);
  assert property (state==YVER  && cnt_r==cycles |=> state==YHOR);

  assert property (state==YHOR  && cnt_r!=cycles |=> state==YHOR);
  assert property (state==YHOR  && cnt_r==cycles |=> state==CVER);

  assert property (state==CVER  && cnt_r!=cycles |=> state==CVER);
  assert property (state==CVER  && cnt_r==cycles |=> state==CHOR);

  assert property (state==CHOR  && cnt_r!=cycles |=> state==CHOR);
  assert property (state==CHOR  && cnt_r==cycles |=> state==OUTLT);

  assert property (state==OUTLT && cnt_r!=cycles |=> state==OUTLT);
  assert property (state==OUTLT && cnt_r==cycles |=> state==OUT);

  assert property (state==OUT   && cnt_r!=cycles |=> state==OUT);
  assert property (state==OUT   && cnt_r==cycles |=> state==IDLE);

  // next combinational decode must match spec
  assert property (state==IDLE  |-> next == (start_i ? LOAD : IDLE));
  assert property (state==LOAD  |-> next == (cnt_r==cycles ? YVER : LOAD));
  assert property (state==YVER  |-> next == (cnt_r==cycles ? YHOR : YVER));
  assert property (state==YHOR  |-> next == (cnt_r==cycles ? CVER : YHOR));
  assert property (state==CVER  |-> next == (cnt_r==cycles ? CHOR : CVER));
  assert property (state==CHOR  |-> next == (cnt_r==cycles ? OUTLT: CHOR));
  assert property (state==OUTLT |-> next == (cnt_r==cycles ? OUT  : OUTLT));
  assert property (state==OUT   |-> next == (cnt_r==cycles ? IDLE : OUT));

  // counter behavior
  assert property (state==IDLE |-> cnt_r==9'd0);
  assert property ((state!=IDLE) |-> cycles>0);
  assert property (state!=IDLE |-> cnt_r<=cycles);
  // increment when staying in same non-IDLE state and not at terminal count
  assert property ($past(rst_n) && state==$past(state) && state!=IDLE &&
                   $past(cnt_r)!=$past(cycles) |-> cnt_r==$past(cnt_r)+1);
  // reset counter after IDLE or after reaching terminal count
  assert property ($past(rst_n) && ($past(state)==IDLE || $past(cnt_r)==$past(cycles)) |-> cnt_r==0);
  // on any state change, counter restarts at 0
  assert property ($past(rst_n) && state!=$past(state) |-> cnt_r==0);

  // done_o pulse only when leaving OUT to IDLE; one-cycle pulse
  assert property ((state==OUT && cnt_r==cycles) |=> done_o);
  assert property (done_o |-> $past(state)==OUT && $past(cnt_r)==$past(cycles));
  assert property (done_o |=> !done_o);
  // when next is not IDLE, done_o must be 0 (matches RTL)
  assert property (next!=IDLE |-> done_o==1'b0);

  // derived flags
  assert property (isluma == ((state==YVER) || (state==YHOR)));
  assert property (isver  == ((state==YVER) || (state==CVER)));

  // Coverage: full path from start to done (through all states in order)
  cover property (
    (state==IDLE && start_i) ##1
    state==LOAD  ##[1:512]
    state==YVER  ##[1:512]
    state==YHOR  ##[1:512]
    state==CVER  ##[1:512]
    state==CHOR  ##[1:512]
    state==OUTLT ##[1:512]
    state==OUT   ##[1:512]
    (state==IDLE && done_o==1'b1)
  );

  // Coverage: each state exits via terminal count to the correct next state
  cover property (state==LOAD  && cnt_r==cycles ##1 state==YVER);
  cover property (state==YVER  && cnt_r==cycles ##1 state==YHOR);
  cover property (state==YHOR  && cnt_r==cycles ##1 state==CVER);
  cover property (state==CVER  && cnt_r==cycles ##1 state==CHOR);
  cover property (state==CHOR  && cnt_r==cycles ##1 state==OUTLT);
  cover property (state==OUTLT && cnt_r==cycles ##1 state==OUT);
  cover property (state==OUT   && cnt_r==cycles ##1 (state==IDLE && done_o));

endmodule

bind db_controller db_controller_sva #(
  .IDLE(3'b000), .LOAD(3'b001), .YVER(3'b011), .YHOR(3'b010),
  .CVER(3'b110), .CHOR(3'b111), .OUTLT(3'b101), .OUT(3'b100)
) db_controller_sva_i (
  .clk(clk),
  .rst_n(rst_n),
  .start_i(start_i),
  .done_o(done_o),
  .cnt_r(cnt_r),
  .state(state),
  .next(next),
  .cycles(cycles),
  .isluma(isluma),
  .isver(isver)
);