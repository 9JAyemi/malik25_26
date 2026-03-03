// SVA for resultcounter
checker resultcounter_sva (
  input  logic        clk,
  input  logic [1:0]  resultID,
  input  logic        newresult,
  input  logic [1:0]  done,
  input  logic        reset,
  input  logic        globalreset,
  input  logic [3:0]  count,
  input  logic [1:0]  curr
);
  default clocking cb @(posedge clk); endclocking

  // Invariants
  assert property (count inside {[4'd0:4'd8)});
  assert property (done == ((count==4'd0) ? curr : 2'b00));

  // Resets and auto-reload
  assert property (globalreset |=> (count==4'd8 && curr==2'b00));
  assert property (!globalreset && reset |=> (count==4'd8 && curr==2'b00));
  assert property (!globalreset && !reset && count==4'd0 |=> (count==4'd8 && curr==2'b00));

  // Decrement and hold rules
  assert property (!globalreset && !reset && count!=4'd0 && newresult && (resultID!=2'b00)
                   |=> (count == $past(count)-4'd1 && curr == $past(resultID)));
  assert property (!globalreset && !reset && count!=4'd0 && (!newresult || (resultID==2'b00))
                   |=> (count == $past(count) && curr == $past(curr)));

  // Count changes only per rules (no unexpected jumps/increments)
  assert property ( (!$past(globalreset) && !$past(reset) && $changed(count))
                    |-> ( ($past(count)==4'd0 && count==4'd8)
                       ||  ($past(count)!=4'd0 && $past(newresult) && $past(resultID)!=2'b00
                            && count==$past(count)-4'd1) ) );

  // Done pulse semantics and cause
  assert property (done!=2'b00 |-> ($past(count)==4'd1 && $past(newresult) && $past(resultID)!=2'b00
                                    && curr==$past(resultID)));
  assert property (done!=2'b00 |=> (done==2'b00 && count==4'd8 && curr==2'b00));

  // Priority: globalreset dominates
  assert property ($past(globalreset) |-> (count==4'd8 && curr==2'b00));

  // No decrement when resultID==0 even if newresult=1
  assert property (!globalreset && !reset && count!=4'd0 && newresult && (resultID==2'b00)
                   |=> (count==$past(count) && curr==$past(curr)));

  // Coverage
  sequence qual_dec; !globalreset && !reset && newresult && (resultID!=2'b00); endsequence
  cover property (count==4'd8 ##1 qual_dec[*7] ##1 (done!=2'b00));
  cover property (done==2'b01);
  cover property (done==2'b10);
  cover property (done==2'b11);
  cover property (!globalreset && !reset && count!=4'd0 && newresult && (resultID==2'b00)
                  ##1 (count==$past(count) && curr==$past(curr)));
  cover property ($rose(globalreset));
  cover property ($rose(reset));
endchecker

bind resultcounter resultcounter_sva rc_chk (
  .clk(clk),
  .resultID(resultID),
  .newresult(newresult),
  .done(done),
  .reset(reset),
  .globalreset(globalreset),
  .count(count),
  .curr(curr)
);