// SVA for regfile
// Bind into the DUT to access internal array "regfile"
bind regfile regfile_sva #(.N(`N), .K(`K)) regfile_sva_i(.*);

module regfile_sva #(parameter int N=`N, K=`K) (
  input  logic                clk,
  input  logic                ld,
  input  logic [K-1:0]        d,
  input  logic [N-1:0]        sa,
  input  logic [N-1:0]        sb,
  input  logic [N-1:0]        a,
  input  logic [N-1:0]        b,
  input  logic [K-1:0]        x
);
  // Access to DUT's internal: regfile [N-1:0] of [K-1:0]
  // default clock and priming to avoid time-0 effects
  default clocking cb @(posedge clk); endclocking
  bit primed; initial primed = 0; always @(posedge clk) primed <= 1;
  default disable iff (!primed);

  // Basic sanity: control must not be X
  assert property ( !$isunknown(ld) );

  // Address validity (when used)
  assert property ( (!$isunknown(sa)) |-> sa < N );
  assert property ( (!$isunknown(sb)) |-> sb < N );
  assert property ( (ld && !$isunknown(d)) |-> d < N );

  // Read data timing: outputs reflect previous-cycle memory at current address
  assert property ( (!$isunknown(sa) && sa < N) |=> a == $past(regfile[sa]) );
  assert property ( (!$isunknown(sb) && sb < N) |=> b == $past(regfile[sb]) );

  // x update behavior
  // x updates only when ld
  assert property ( $changed(x) |-> ld );
  // When ld, x equals the same read value as a in that cycle
  assert property ( (ld && !$isunknown(sa) && sa < N) |=> x == $past(regfile[sa]) );

  // Write behavior: on ld, location d gets value d
  assert property ( (ld && !$isunknown(d) && d < N) |=> regfile[$past(d)] == $past(d) );

  // Useful cross-check: on ld, a and x match (same-cycle NBAs)
  assert property ( ld |=> ($past(a) == $past(x)) );

  // Coverage
  cover property ( ld );
  cover property ( ld && (sa == d) );
  cover property ( ld && (sb == d) );
  cover property ( sa == sb );
  cover property ( $changed(a) );
  cover property ( $changed(b) );
  cover property ( $changed(x) );
  cover property ( ld && (d == 0) );
  cover property ( ld && (d == N-1) );
endmodule