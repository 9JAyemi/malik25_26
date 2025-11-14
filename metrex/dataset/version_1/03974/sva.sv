// SVA for AllignAdderProcess
// Focus: cycle-accurate pipeline forwarding, idle path passthrough, active path alignment, sticky-bit behavior, exponent update, and branch selection

module AllignAdderProcess_sva
(
  input logic                clock,
  input logic [31:0]         z_postSpecial,
  input logic [3:0]          Opcode_Special,
  input logic                idle_Special,
  input logic [35:0]         cout_Special,
  input logic [35:0]         zout_Special,
  input logic [31:0]         sout_Special,
  input logic [7:0]          difference_Special,
  input logic [7:0]          InsTagSpecial,

  input logic                idle_Allign,
  input logic [35:0]         cout_Allign,
  input logic [35:0]         zout_Allign,
  input logic [31:0]         sout_Allign,
  input logic [3:0]          Opcode_Allign,
  input logic [31:0]         z_postAllign,
  input logic [7:0]          InsTagAllign
);

  // DUT constant mirror
  localparam bit put_idle = 1'b1;

  // Helpers
  function automatic bit c_gt_z(input logic [7:0] c_enc, input logic [7:0] z_enc);
    logic signed [7:0] ce, ze;
    begin
      ce = $signed(c_enc - 8'd127);
      ze = $signed(z_enc - 8'd127);
      return (ce > ze);
    end
  endfunction

  function automatic logic [26:0] shift_and_set_lsb(input logic [26:0] m, input logic [7:0] d);
    logic [26:0] s;
    begin
      s = m >> d;
      s[0] = m[0] | m[1];
      return s;
    end
  endfunction

  default clocking @(posedge clock); endclocking
  default disable iff ($initstate);

  // 1-cycle forwarding for simple pipeline fields
  assert property (InsTagAllign  == $past(InsTagSpecial));
  assert property (Opcode_Allign == $past(Opcode_Special));
  assert property (z_postAllign  == $past(z_postSpecial));
  assert property (idle_Allign   == $past(idle_Special));
  assert property (sout_Allign   == $past(sout_Special));

  // Idle path: strict passthrough of z/c bundles
  assert property ( $past(idle_Special) == put_idle
                    |-> (zout_Allign == $past(zout_Special) &&
                         cout_Allign == $past(cout_Special)) );

  // Active path, branch c_exp > z_exp: align z toward c, pass c
  assert property ( ($past(idle_Special) != put_idle) &&
                    c_gt_z($past(cout_Special[34:27]), $past(zout_Special[34:27]))
                    |->
                    ( // sign and exponent update
                      zout_Allign[35]     == $past(zout_Special[35]) &&
                      zout_Allign[34:27]  == ($past(zout_Special[34:27]) + $past(difference_Special)) &&
                      // mantissa shift with LSB overwrite (sticky/round OR)
                      zout_Allign[26:0]   == shift_and_set_lsb($past(zout_Special[26:0]), $past(difference_Special)) &&
                      // pass-through the other operand
                      cout_Allign         == $past(cout_Special)
                    )
                  );

  // Active path, branch c_exp <= z_exp: align c toward z, pass z
  assert property ( ($past(idle_Special) != put_idle) &&
                    !c_gt_z($past(cout_Special[34:27]), $past(zout_Special[34:27]))
                    |->
                    ( cout_Allign[35]     == $past(cout_Special[35]) &&
                      cout_Allign[34:27]  == ($past(cout_Special[34:27]) + $past(difference_Special)) &&
                      cout_Allign[26:0]   == shift_and_set_lsb($past(cout_Special[26:0]), $past(difference_Special)) &&
                      zout_Allign         == $past(zout_Special)
                    )
                  );

  // Minimal but meaningful coverage
  cover property ( $past(idle_Special) == put_idle );
  cover property ( ($past(idle_Special) != put_idle) &&
                   c_gt_z($past(cout_Special[34:27]), $past(zout_Special[34:27])) );
  cover property ( ($past(idle_Special) != put_idle) &&
                   !c_gt_z($past(cout_Special[34:27]), $past(zout_Special[34:27])) );

  // Exercise sticky/LSB behavior for both branches with diff=0 and diff>0
  cover property ( ($past(idle_Special) != put_idle) &&
                   c_gt_z($past(cout_Special[34:27]), $past(zout_Special[34:27])) &&
                   ($past(difference_Special) == 8'd0) );
  cover property ( ($past(idle_Special) != put_idle) &&
                   !c_gt_z($past(cout_Special[34:27]), $past(zout_Special[34:27])) &&
                   ($past(difference_Special) >= 8'd2) );

endmodule

// Bind into DUT (adjust instance pathing if needed)
bind AllignAdderProcess AllignAdderProcess_sva sva_i
(
  .clock,
  .z_postSpecial,
  .Opcode_Special,
  .idle_Special,
  .cout_Special,
  .zout_Special,
  .sout_Special,
  .difference_Special,
  .InsTagSpecial,
  .idle_Allign,
  .cout_Allign,
  .zout_Allign,
  .sout_Allign,
  .Opcode_Allign,
  .z_postAllign,
  .InsTagAllign
);