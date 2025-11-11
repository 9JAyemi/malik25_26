// Bindable SVA checker for SpecialCases
bind SpecialCases SpecialCases_sva sva();

module SpecialCases_sva;

  // Clocking/reset
  default clocking cb @(posedge clock); endclocking
  // For functional assertions, disable during reset
  default disable iff (reset);

  // Encodings from DUT
  localparam logic [1:0] NO_IDLE    = 2'b00;
  localparam logic [1:0] ALIGN_IDLE = 2'b01;
  localparam logic [1:0] PUT_IDLE   = 2'b10;

  // Recompute fields from inputs (match DUT math)
  wire        a_s   = ain_Special[31];
  wire [7:0]  a_e   = ain_Special[30:23] - 8'd127;
  wire [23:0] a_m   = {1'b0, ain_Special[22:0]};
  wire        b_s   = bin_Special[31];
  wire [7:0]  b_e   = bin_Special[30:23] - 8'd127;
  wire [23:0] b_m   = {1'b0, bin_Special[22:0]};
  wire        c_s   = cin_Special[31];
  wire [7:0]  c_e   = cin_Special[30:23] - 8'd127;
  wire [26:0] c_m   = {cin_Special[22:0],3'd0};

  wire signed [7:0] a_es = a_e;
  wire signed [7:0] b_es = b_e;
  wire signed [7:0] c_es = c_e;

  // Conditions per DUT
  wire nan_a   = (a_e == 8'd128) && (a_m != 24'd0);
  wire nan_b   = (b_e == 8'd128) && (b_m != 24'd0);
  wire inf_a   = (a_e == 8'd128) && (a_m == 24'd0);
  wire inf_b   = (b_e == 8'd128) && (b_m == 24'd0);
  wire a_zero  = (a_es == -8'sd127) && (a_m == 24'd0);
  wire b_zero  = (b_es == -8'sd127) && (b_m == 24'd0);
  wire mode00  = (mode_Special == 2'b00);
  wire zsign   = a_s ^ b_s;

  // Default path condition (final else)
  wire default_path = !(nan_a || nan_b || inf_a || inf_b || a_zero || b_zero || mode00);

  // Header/sideband passthrough every active cycle
  assert property (1 |-> (InsTag_Special      == InsTagFSMOut
                       && modeout_Special     == mode_Special
                       && operationout_Special== operation_Special
                       && NatLogFlagout_Special== NatLogFlag_Special));

  // Reset behavior for idle
  assert property (@(posedge clock) reset |-> idle_Special == NO_IDLE);

  // NaN on A or B
  assert property ((nan_a || nan_b)
                   |-> (idle_Special == ALIGN_IDLE
                        && aout_Special == {a_s, a_e + 8'd127, a_m}
                        && bout_Special == {b_s, b_e + 8'd127, b_m}
                        && cout_Special == {c_s, c_e + 8'd127, c_m}
                        && zout_Special == {1'b1, 8'd255, 1'b1, 26'd0}
                        && sout_Special == 32'd0));

  // A is +/−Inf, B is zero/subnormal zero -> NaN
  assert property ((inf_a && (b_es == -8'sd127) && (b_m == 24'd0) && !nan_b)
                   |-> (idle_Special == ALIGN_IDLE
                        && aout_Special == {a_s, a_e, a_m}
                        && bout_Special == {b_s, b_e, b_m}
                        && cout_Special == {c_s, c_e, c_m}
                        && zout_Special == {1'b1, 8'd255, 1'b1, 26'd0}
                        && sout_Special == 32'd0));

  // A is +/−Inf, B not zero -> +/-Inf
  assert property ((inf_a && !((b_es == -8'sd127) && (b_m == 24'd0)) && !nan_b)
                   |-> (idle_Special == ALIGN_IDLE
                        && aout_Special == {a_s, a_e, a_m}
                        && bout_Special == {b_s, b_e, b_m}
                        && cout_Special == {c_s, c_e, c_m}
                        && zout_Special == {zsign, 8'd255, 27'd0}
                        && sout_Special == 32'd0));

  // B is +/−Inf -> +/-Inf
  assert property ((inf_b && !nan_a)
                   |-> (idle_Special == ALIGN_IDLE
                        && aout_Special == {a_s, a_e, a_m}
                        && bout_Special == {b_s, b_e, b_m}
                        && cout_Special == {c_s, c_e, c_m}
                        && zout_Special == {zsign, 8'd255, 27'd0}
                        && sout_Special == 32'd0));

  // A is zero/subnormal zero branch
  assert property (a_zero
                   |-> (idle_Special == PUT_IDLE
                        && aout_Special == {a_s, a_e + 8'd127, 1'b1, a_m[22:0]}
                        && bout_Special == {b_s, b_e + 8'd127, 1'b1, b_m[22:0]}
                        && cout_Special == {c_s, c_e + 8'd127, c_m}
                        && zout_Special == {zsign, 8'd0, 27'd0}
                        && sout_Special == {c_s, c_e + 8'd127, c_m[25:3]}));

  // B is zero/subnormal zero branch
  assert property (b_zero
                   |-> (idle_Special == PUT_IDLE
                        && aout_Special == {a_s, a_e + 8'd127, 1'b1, a_m[22:0]}
                        && bout_Special == {b_s, b_e + 8'd127, 1'b1, b_m[22:0]}
                        && cout_Special == {c_s, c_e + 8'd127, c_m}
                        && zout_Special == {zsign, 8'd0, 27'd0}
                        && sout_Special == {c_s, c_e + 8'd127, c_m[25:3]}));

  // mode_Special == 2'b00 branch
  assert property (mode00
                   |-> (idle_Special == PUT_IDLE
                        && aout_Special == {a_s, a_e + 8'd127, 1'b1, a_m[22:0]}
                        && bout_Special == {b_s, b_e + 8'd127, 1'b1, b_m[22:0]}
                        && cout_Special == {c_s, c_e + 8'd127, c_m}
                        && zout_Special == {zsign, 8'd0, 27'd0}
                        && sout_Special == {c_s, c_e + 8'd127, c_m[25:3]}));

  // Default (final else): common outs
  assert property (default_path
                   |-> (idle_Special == NO_IDLE
                        && cout_Special == {c_s, c_e + 8'd127, c_m}
                        && zout_Special == 36'd0
                        && sout_Special == 32'd0));

  // Default: A formatting
  assert property (default_path && (a_es == -8'sd127)
                   |-> aout_Special == {a_s, -8'sd126, a_m});
  assert property (default_path && (a_es != -8'sd127)
                   |-> aout_Special == {a_s, a_e + 8'd127, 1'b1, a_m[22:0]});

  // Default: B formatting
  assert property (default_path && (b_es == -8'sd127)
                   |-> bout_Special == {b_s, -8'sd126, b_m});
  assert property (default_path && (b_es != -8'sd127)
                   |-> bout_Special == {b_s, b_e + 8'd127, 1'b1, b_m[22:0]});

  // Minimal functional coverage of all branches
  cover property (nan_a || nan_b);
  cover property (inf_a && (b_es == -8'sd127) && (b_m == 0));
  cover property (inf_a && !((b_es == -8'sd127) && (b_m == 0)));
  cover property (inf_b);
  cover property (a_zero);
  cover property (b_zero);
  cover property (mode00);
  cover property (default_path && (a_es == -8'sd127));
  cover property (default_path && (b_es == -8'sd127));
  cover property (default_path && (a_es != -8'sd127) && (b_es != -8'sd127));

endmodule