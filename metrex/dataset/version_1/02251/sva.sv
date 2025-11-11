// SVA checker for CSADD
module CSADD_sva (
  input logic clk, rst,
  input logic x, y, ld,
  input logic sum, sc
);

  default clocking cb @(posedge clk); endclocking

  // Basic sanity (no X on controls/inputs)
  assert property (cb !$isunknown({rst, ld, x, y}))
    else $error("X/Z on control/input");

  // Outputs known once out of reset
  assert property (cb disable iff (rst) !$isunknown({sum, sc}))
    else $error("X/Z on outputs");

  // Asynchronous reset takes effect immediately
  assert property (@(posedge rst) ##0 (sum==0 && sc==0))
    else $error("Async reset failed");

  // Synchronous reset holds outputs at 0
  assert property (cb rst |-> (sum==0 && sc==0))
    else $error("Sync reset hold failed");

  // ld clears state on next cycle
  assert property (cb (!rst && ld) |=> (sum==0 && sc==0))
    else $error("ld clear failed");

  // Core functionality: next-state equals 3:2 add of x,y,prev sc
  // Concise, checks both sum and carry together
  assert property (cb disable iff (rst || ld)
                   1 |=> {sc, sum} == ($past(x) + $past(y) + $past(sc)))
    else $error("Functional add mismatch");

  // Optional explicit parity/carry checks (redundant with above but helpful for debug)
  assert property (cb disable iff (rst || ld)
                   1 |=> sum == ($past(x) ^ $past(y) ^ $past(sc)))
    else $error("Sum parity mismatch");

  assert property (cb disable iff (rst || ld)
                   1 |=> sc == (($past(x)&$past(y)) | ($past(sc)&($past(x)^$past(y)))))
    else $error("Carry majority mismatch");

  // ----------------
  // Coverage
  // ----------------
  // Reset pulse and release
  cover property (@(posedge rst) ##1 !rst);

  // ld pulse clears state
  cover property (cb !rst && ld ##1 (sum==0 && sc==0));

  // Normal op: generate carry (>=2 ones among x,y,sc_prev)
  cover property (cb disable iff (rst || ld)
                  (($past(x)&$past(y)) | ($past(x)&$past(sc)) | ($past(y)&$past(sc)))
                  ##1 sc);

  // Normal op: no carry
  cover property (cb disable iff (rst || ld)
                  ~(($past(x)&$past(y)) | ($past(x)&$past(sc)) | ($past(y)&$past(sc)))
                  ##1 !sc);

  // Sum=1 and Sum=0 cases under normal op
  cover property (cb disable iff (rst || ld)
                  ($past(x)^$past(y)^$past(sc)) ##1 sum);
  cover property (cb disable iff (rst || ld)
                  ~($past(x)^$past(y)^$past(sc)) ##1 !sum);

endmodule

// Bind into DUT
bind CSADD CSADD_sva i_CSADD_sva (
  .clk(clk), .rst(rst),
  .x(x), .y(y), .ld(ld),
  .sum(sum), .sc(sc)
);