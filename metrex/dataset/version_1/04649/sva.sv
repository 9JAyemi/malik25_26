// SVA for AllignAdder
// Bind this file to the DUT. Focused, concise checks with essential coverage.

module AllignAdder_sva #(parameter PUT_IDLE = 1'b1) (
  input logic                  clock,
  input logic                  idle_Special,
  input logic [35:0]           cout_Special,
  input logic [35:0]           zout_Special,
  input logic [31:0]           sout_Special,
  input logic [7:0]            difference_Special,
  input logic                  idle_Allign,
  input logic [35:0]           cout_Allign,
  input logic [35:0]           zout_Allign,
  input logic [31:0]           sout_Allign
);

  // default clock
  default clocking cb @(posedge clock); endclocking

  // guard for $past
  logic past_valid;
  initial past_valid = 1'b0;
  always_ff @(posedge clock) past_valid <= 1'b1;

  // helper: expected mantissa with post-fix sticky bit (as coded in DUT)
  function automatic logic [26:0] exp_mant(input logic [26:0] m, input logic [7:0] d);
    logic [26:0] sh; logic sticky;
    begin
      sh     = m >> d;
      sticky = m[0] | m[1];  // matches DUT
      exp_mant = {sh[26:1], sticky};
    end
  endfunction

  // signed exponent compare (matches DUT decode and $signed usage)
  function automatic logic c_gt_z(input logic [35:0] c, input logic [35:0] z);
    logic signed [7:0] ce, ze;
    begin
      ce = c[34:27] - 8'd127;
      ze = z[34:27] - 8'd127;
      c_gt_z = (ce > ze);
    end
  endfunction

  // X/Z checks on inputs and outputs
  assert property (cb disable iff (!past_valid)
    !$isunknown({idle_Special, difference_Special, cout_Special, zout_Special})
  ) else $error("AllignAdder: X/Z on inputs");

  assert property (cb
    !$isunknown({idle_Allign, cout_Allign, zout_Allign, sout_Allign})
  ) else $error("AllignAdder: X/Z on outputs");

  // Registered copies
  assert property (cb disable iff (!past_valid)
    idle_Allign == $past(idle_Special)
  ) else $error("idle_Allign should be 1-cycle copy of idle_Special");

  assert property (cb disable iff (!past_valid)
    sout_Allign == $past(sout_Special)
  ) else $error("sout_Allign should be 1-cycle copy of sout_Special");

  // Idle path: full passthrough of cout/zout
  assert property (cb disable iff (!past_valid)
    $past(idle_Special == PUT_IDLE) |-> (
      (zout_Allign == $past(zout_Special)) &&
      (cout_Allign == $past(cout_Special))
    )
  ) else $error("Idle passthrough mismatch");

  // Non-idle, c_exp > z_exp: align Z, pass C
  assert property (cb disable iff (!past_valid)
    $past(idle_Special != PUT_IDLE && c_gt_z($past(cout_Special), $past(zout_Special))) |->
    (
      // zout_Allign fields
      (zout_Allign[35]    == $past(zout_Special[35])) &&
      (zout_Allign[34:27] == ( ($past(zout_Special[34:27]) - 8'd127) + $past(difference_Special) + 8'd127 )) &&
      (zout_Allign[26:0]  == exp_mant($past(zout_Special[26:0]), $past(difference_Special))) &&
      // cout_Allign passthrough
      (cout_Allign        == $past(cout_Special))
    )
  ) else $error("c>z alignment (Z adjusted) mismatch");

  // Non-idle, c_exp <= z_exp: align C, pass Z
  assert property (cb disable iff (!past_valid)
    $past(idle_Special != PUT_IDLE && !c_gt_z($past(cout_Special), $past(zout_Special))) |->
    (
      // cout_Allign fields
      (cout_Allign[35]    == $past(cout_Special[35])) &&
      (cout_Allign[34:27] == ( ($past(cout_Special[34:27]) - 8'd127) + $past(difference_Special) + 8'd127 )) &&
      (cout_Allign[26:0]  == exp_mant($past(cout_Special[26:0]), $past(difference_Special))) &&
      // zout_Allign passthrough
      (zout_Allign        == $past(zout_Special))
    )
  ) else $error("c<=z alignment (C adjusted) mismatch");

  // Minimal functional coverage
  cover property (cb disable iff (!past_valid)
    $past(idle_Special == PUT_IDLE)
  ); // idle passthrough seen

  cover property (cb disable iff (!past_valid)
    $past(idle_Special != PUT_IDLE && c_gt_z($past(cout_Special), $past(zout_Special)) && ($past(difference_Special)==8'd0))
  ); // c>z with diff=0

  cover property (cb disable iff (!past_valid)
    $past(idle_Special != PUT_IDLE && c_gt_z($past(cout_Special), $past(zout_Special)) && ($past(difference_Special)>=8'd2))
  ); // c>z with diff>=2 (sticky effect meaningful)

  cover property (cb disable iff (!past_valid)
    $past(idle_Special != PUT_IDLE && !c_gt_z($past(cout_Special), $past(zout_Special)) && ($past(difference_Special)>=8'd1))
  ); // c<=z with diff>=1

endmodule

// Bind to DUT
bind AllignAdder AllignAdder_sva #(.PUT_IDLE(put_idle)) u_AllignAdder_sva (.*);