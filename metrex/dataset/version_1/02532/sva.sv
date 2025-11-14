// SVA for SpecialAdd
// Bind into the DUT or include inside the module for inline checking.
module SpecialAdd_sva
(
  input  logic         clock,
  input  logic         reset,
  input  logic [31:0]  cin_Special,
  input  logic [31:0]  zin_Special,
  input  logic         idle_Special,
  input  logic [7:0]   difference_Special,
  input  logic [35:0]  cout_Special,
  input  logic [35:0]  zout_Special,
  input  logic [31:0]  sout_Special
);

  // Helper decode
  function automatic logic signed [8:0] unbias (input logic [7:0] e);
    unbias = $signed({1'b0,e}) - 9'sd127;
  endfunction
  function automatic logic [26:0] ext_m (input logic [22:0] m);
    ext_m = {m,3'b000};
  endfunction
  function automatic logic [35:0] ext32_36 (input logic [31:0] x);
    ext32_36 = {4'b0,x};
  endfunction

  // Current-cycle decodes (used with $past() in assertions)
  logic       c_s, z_s;
  logic [7:0] c_er, z_er;           // raw exponent
  logic [22:0] c_mr, z_mr;          // raw mantissa
  logic signed [8:0] c_e, z_e;      // unbiased exponent
  logic [26:0] c_m, z_m;            // extended mantissa

  assign c_s  = cin_Special[31];
  assign c_er = cin_Special[30:23];
  assign c_mr = cin_Special[22:0];
  assign z_s  = zin_Special[31];
  assign z_er = zin_Special[30:23];
  assign z_mr = zin_Special[22:0];

  assign c_e = unbias(c_er);
  assign z_e = unbias(z_er);
  assign c_m = ext_m(c_mr);
  assign z_m = ext_m(z_mr);

  // Classifiers
  function automatic bit is_nan(input logic [7:0] e, input logic [22:0] m);
    return (e==8'hFF) && (m!=0);
  endfunction
  function automatic bit is_inf(input logic [7:0] e, input logic [22:0] m);
    return (e==8'hFF) && (m==0);
  endfunction
  function automatic bit is_zero(input logic [7:0] e, input logic [22:0] m);
    return (e==8'h00) && (m==0);
  endfunction
  function automatic bit is_subn(input logic [7:0] e, input logic [22:0] m);
    return (e==8'h00) && (m!=0);
  endfunction

  // Encode DUT's mutually-exclusive else-if chain as a case ID
  function automatic int scase(
    input logic [7:0] ce, ze,
    input logic [22:0] cm, zm
  );
    bit nan_any = is_nan(ce,cm) || is_nan(ze,zm);
    if (nan_any)                               return 0; // NaN
    else if (is_inf(ce,cm))                    return 1; // c Inf
    else if (is_inf(ze,zm))                    return 2; // z Inf
    else if (is_zero(ce,cm) && is_zero(ze,zm)) return 3; // both zero
    else if (is_zero(ce,cm))                   return 4; // c zero
    else if (is_zero(ze,zm))                   return 5; // z zero
    else                                       return 6; // normal/pack path
  endfunction

  // Past-valid guard
  logic past_valid;
  always_ff @(posedge clock) begin
    if (reset) past_valid <= 1'b0;
    else       past_valid <= 1'b1;
  end

  default clocking cb @(posedge clock); endclocking

  // Reset behavior
  assert property (cb disable iff (1'b0)
                   reset |-> (idle_Special==1'b0));

  // difference_Special = |z_e - c_e| every non-reset cycle
  assert property (cb disable iff (reset)
                   past_valid |-> difference_Special
                                == ( ($unsigned($abs($past(z_e) - $past(c_e))))[7:0] ));

  // Special-case: any NaN -> quiet NaN, pass-through cout/zout, idle=1
  assert property (cb disable iff (reset)
    past_valid && ($past(scase($past(c_er),$past(z_er),$past(c_mr),$past(z_mr)))==0) |-> 
      (sout_Special[31]==1'b1 &&
       sout_Special[30:23]==8'hFF &&
       sout_Special[22]==1'b1 &&
       sout_Special[21:0]==22'd0) &&
      (cout_Special==ext32_36($past(cin_Special))) &&
      (zout_Special==ext32_36($past(zin_Special))) &&
      (idle_Special==1'b1) );

  // c Inf (no NaN) -> copy c to sout, pass-through, idle=1
  assert property (cb disable iff (reset)
    past_valid && ($past(scase($past(c_er),$past(z_er),$past(c_mr),$past(z_mr)))==1) |-> 
      (sout_Special == { $past(c_s), 8'hFF, 23'd0 }) &&
      (cout_Special==ext32_36($past(cin_Special))) &&
      (zout_Special==ext32_36($past(zin_Special))) &&
      (idle_Special==1'b1) );

  // z Inf (no NaN, no c Inf) -> copy z to sout, pass-through, idle=1
  assert property (cb disable iff (reset)
    past_valid && ($past(scase($past(c_er),$past(z_er),$past(c_mr),$past(z_mr)))==2) |-> 
      (sout_Special == { $past(z_s), 8'hFF, 23'd0 }) &&
      (cout_Special==ext32_36($past(cin_Special))) &&
      (zout_Special==ext32_36($past(zin_Special))) &&
      (idle_Special==1'b1) );

  // Both zeros -> zero with sign AND, pass-through, idle=1
  assert property (cb disable iff (reset)
    past_valid && ($past(scase($past(c_er),$past(z_er),$past(c_mr),$past(z_mr)))==3) |-> 
      (sout_Special == { ($past(c_s)&$past(z_s)), 8'h00, 23'd0 }) &&
      (cout_Special==ext32_36($past(cin_Special))) &&
      (zout_Special==ext32_36($past(zin_Special))) &&
      (idle_Special==1'b1) );

  // c zero only -> copy z to sout, pass-through, idle=1
  assert property (cb disable iff (reset)
    past_valid && ($past(scase($past(c_er),$past(z_er),$past(c_mr),$past(z_mr)))==4) |-> 
      (sout_Special == { $past(z_s), $past(z_er), $past(z_mr) }) &&
      (cout_Special==ext32_36($past(cin_Special))) &&
      (zout_Special==ext32_36($past(zin_Special))) &&
      (idle_Special==1'b1) );

  // z zero only -> copy c to sout, pass-through, idle=1
  assert property (cb disable iff (reset)
    past_valid && ($past(scase($past(c_er),$past(z_er),$past(c_mr),$past(z_mr)))==5) |-> 
      (sout_Special == { $past(c_s), $past(c_er), $past(c_mr) }) &&
      (cout_Special==ext32_36($past(cin_Special))) &&
      (zout_Special==ext32_36($past(zin_Special))) &&
      (idle_Special==1'b1) );

  // Normal/pack path: sout cleared
  assert property (cb disable iff (reset)
    past_valid && ($past(scase($past(c_er),$past(z_er),$past(c_mr),$past(z_mr)))==6) |-> 
      (sout_Special == 32'h0) );

  // cout_Special packing (normal/pack path)
  // c subnormal
  assert property (cb disable iff (reset)
    past_valid &&
    ($past(scase($past(c_er),$past(z_er),$past(c_mr),$past(z_mr)))==6) &&
    ($past(c_er)==8'h00) |-> 
      (cout_Special[35]    == $past(c_s)) &&
      ($signed(cout_Special[34:27]) == -9'sd126) &&
      (cout_Special[26:0]  == ext_m($past(c_mr))) );

  // c normal
  assert property (cb disable iff (reset)
    past_valid &&
    ($past(scase($past(c_er),$past(z_er),$past(c_mr),$past(z_mr)))==6) &&
    ($past(c_er)!=8'h00) |-> 
      (cout_Special[35]    == $past(c_s)) &&
      (cout_Special[34:27] == $past(c_er)) &&
      (cout_Special[26]    == 1'b1) &&
      (cout_Special[25:0]  == ext_m($past(c_mr))[25:0]) );

  // zout_Special packing (normal/pack path)
  // z subnormal
  assert property (cb disable iff (reset)
    past_valid &&
    ($past(scase($past(c_er),$past(z_er),$past(c_mr),$past(z_mr)))==6) &&
    ($past(z_er)==8'h00) |-> 
      (zout_Special[35]    == $past(z_s)) &&
      ($signed(zout_Special[34:27]) == -9'sd126) &&
      (zout_Special[26:0]  == ext_m($past(z_mr))) );

  // z normal
  assert property (cb disable iff (reset)
    past_valid &&
    ($past(scase($past(c_er),$past(z_er),$past(c_mr),$past(z_mr)))==6) &&
    ($past(z_er)!=8'h00) |-> 
      (zout_Special[35]    == $past(z_s)) &&
      (zout_Special[34:27] == $past(z_er)) &&
      (zout_Special[26]    == 1'b1) &&
      (zout_Special[25:0]  == ext_m($past(z_mr))[25:0]) );

  // Idle control: special-cases -> idle=1, pack path with any normal -> idle=0
  assert property (cb disable iff (reset)
    past_valid && ($past(scase($past(c_er),$past(z_er),$past(c_mr),$past(z_mr))) inside {0,1,2,3,4,5}) |-> (idle_Special==1'b1) );
  assert property (cb disable iff (reset)
    past_valid &&
    ($past(scase($past(c_er),$past(z_er),$past(c_mr),$past(z_mr)))==6) &&
    ( ($past(c_er)!=8'h00) || ($past(z_er)!=8'h00) ) |-> (idle_Special==1'b0) );

  // ------------- Coverage -------------
  cover property (cb past_valid && $past(scase($past(c_er),$past(z_er),$past(c_mr),$past(z_mr)))==0); // NaN any
  cover property (cb past_valid && $past(scase($past(c_er),$past(z_er),$past(c_mr),$past(z_mr)))==1); // c Inf
  cover property (cb past_valid && $past(scase($past(c_er),$past(z_er),$past(c_mr),$past(z_mr)))==2); // z Inf
  cover property (cb past_valid && $past(scase($past(c_er),$past(z_er),$past(c_mr),$past(z_mr)))==3); // both zero
  cover property (cb past_valid && $past(scase($past(c_er),$past(z_er),$past(c_mr),$past(z_mr)))==4); // c zero
  cover property (cb past_valid && $past(scase($past(c_er),$past(z_er),$past(c_mr),$past(z_mr)))==5); // z zero
  cover property (cb past_valid &&
                  $past(scase($past(c_er),$past(z_er),$past(c_mr),$past(z_mr)))==6 &&
                  ($past(c_er)!=8'h00) && ($past(z_er)!=8'h00)); // both normal
  cover property (cb past_valid &&
                  $past(scase($past(c_er),$past(z_er),$past(c_mr),$past(z_mr)))==6 &&
                  ($past(c_er)==8'h00) && ($past(z_er)==8'h00)); // both subnormal
  cover property (cb past_valid &&
                  difference_Special==8'd0);
  cover property (cb past_valid &&
                  difference_Special==8'd255);

endmodule

// Bind example:
// bind SpecialAdd SpecialAdd_sva sva (.*);