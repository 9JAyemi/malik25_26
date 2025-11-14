// SVA for priority_encoder_mux
// Bind this module to the DUT. Concise, checks core functionality, with basic coverage.

module priority_encoder_mux_sva (priority_encoder_mux dut);

  // Pseudo "combinational clock" for concurrent assertions
  event comb_ev;
  always @* -> comb_ev;

  // Golden models (purely from DUT inputs)
  function automatic [2:0] exp_pos(input logic [7:0] in);
    logic [7:0] p, p1, p2, p3, p4;
    p  = ~in;
    p1 = p  | {p[6:0], 1'b0};
    p2 = p1 | {p1[5:0], 2'b0};
    p3 = p2 | {p2[3:0], 4'b0};
    p4 = p3 | {p3[1:0], 6'b0};
    exp_pos = p4[7:5] - 3'd1;
  endfunction

  function automatic [7:0] exp_mux_out(input logic [2047:0] mux_in, input logic [7:0] sel);
    exp_mux_out = mux_in[sel*8 +: 8];
  endfunction

  function automatic [3:0] exp_dec(input logic [1:0] en);
    case (en)
      2'b00: exp_dec = 4'b0001;
      2'b01: exp_dec = 4'b0010;
      2'b10: exp_dec = 4'b0100;
      2'b11: exp_dec = 4'b1000;
    endcase
  endfunction

  // Core assertions
  // Priority encoder output matches golden model (no X on inputs)
  assert property (@(comb_ev) !$isunknown(dut.in) |-> (dut.pos == exp_pos(dut.in)))
    else $error("pos mismatch: in=%0h pos=%0d exp=%0d", dut.in, dut.pos, exp_pos(dut.in));

  // Mux + decoder -> gated outputs match golden model (no X on driving inputs)
  assert property (@(comb_ev)
    !$isunknown({dut.sel, dut.enable, dut.mux_in}) |->
    (dut.out1 == ((dut.enable==2'b00) ? exp_mux_out(dut.mux_in, dut.sel) : 8'b0)) &&
    (dut.out2 == ((dut.enable==2'b01) ? exp_mux_out(dut.mux_in, dut.sel) : 8'b0)) &&
    (dut.out3 == ((dut.enable==2'b10) ? exp_mux_out(dut.mux_in, dut.sel) : 8'b0)) &&
    (dut.out4 == ((dut.enable==2'b11) ? exp_mux_out(dut.mux_in, dut.sel) : 8'b0)))
    else $error("Output gating/mux mismatch");

  // Decoder one-hot expectation
  assert property (@(comb_ev) !$isunknown(dut.enable) |-> $onehot(exp_dec(dut.enable)))
    else $error("Enable decode not one-hot");

  // No-X propagation on outputs when inputs are known
  assert property (@(comb_ev)
    !$isunknown({dut.sel, dut.enable, dut.mux_in}) |-> !$isunknown({dut.out1,dut.out2,dut.out3,dut.out4}))
    else $error("Outputs contain X with known inputs");

  // No-X on pos when in is known
  assert property (@(comb_ev) !$isunknown(dut.in) |-> !$isunknown(dut.pos))
    else $error("pos contains X with known in");

  // Mutually exclusive drive: when enable known, only the selected output equals mux_out; others are zero
  // (Stronger duplication of the gating check above, but catches accidental multiple enables even when mux_out==0 by checking indices)
  assert property (@(comb_ev)
    !$isunknown(dut.enable) |->
      ((dut.enable==2'b00) -> (dut.out2==8'b0 && dut.out3==8'b0 && dut.out4==8'b0)) and
      ((dut.enable==2'b01) -> (dut.out1==8'b0 && dut.out3==8'b0 && dut.out4==8'b0)) and
      ((dut.enable==2'b10) -> (dut.out1==8'b0 && dut.out2==8'b0 && dut.out4==8'b0)) and
      ((dut.enable==2'b11) -> (dut.out1==8'b0 && dut.out2==8'b0 && dut.out3==8'b0)))
    else $error("Multiple outputs driven for single enable");

  // Lightweight functional coverage
  // Enable values
  cover property (@(comb_ev) dut.enable == 2'b00);
  cover property (@(comb_ev) dut.enable == 2'b01);
  cover property (@(comb_ev) dut.enable == 2'b10);
  cover property (@(comb_ev) dut.enable == 2'b11);

  // sel extremes
  cover property (@(comb_ev) dut.sel == 8'h00);
  cover property (@(comb_ev) dut.sel == 8'hFF);

  // Observe non-zero mux_out propagated to each output
  cover property (@(comb_ev)
    (dut.enable==2'b00) && (exp_mux_out(dut.mux_in,dut.sel) != 8'h00) && (dut.out1 == exp_mux_out(dut.mux_in,dut.sel)));
  cover property (@(comb_ev)
    (dut.enable==2'b01) && (exp_mux_out(dut.mux_in,dut.sel) != 8'h00) && (dut.out2 == exp_mux_out(dut.mux_in,dut.sel)));
  cover property (@(comb_ev)
    (dut.enable==2'b10) && (exp_mux_out(dut.mux_in,dut.sel) != 8'h00) && (dut.out3 == exp_mux_out(dut.mux_in,dut.sel)));
  cover property (@(comb_ev)
    (dut.enable==2'b11) && (exp_mux_out(dut.mux_in,dut.sel) != 8'h00) && (dut.out4 == exp_mux_out(dut.mux_in,dut.sel)));

  // pos distribution coverage (when input is known)
  cover property (@(comb_ev) !$isunknown(dut.in) && dut.pos == 3'd0);
  cover property (@(comb_ev) !$isunknown(dut.in) && dut.pos == 3'd1);
  cover property (@(comb_ev) !$isunknown(dut.in) && dut.pos == 3'd2);
  cover property (@(comb_ev) !$isunknown(dut.in) && dut.pos == 3'd3);
  cover property (@(comb_ev) !$isunknown(dut.in) && dut.pos == 3'd4);
  cover property (@(comb_ev) !$isunknown(dut.in) && dut.pos == 3'd5);
  cover property (@(comb_ev) !$isunknown(dut.in) && dut.pos == 3'd6);
  cover property (@(comb_ev) !$isunknown(dut.in) && dut.pos == 3'd7);

  // Interesting input patterns
  cover property (@(comb_ev) dut.in == 8'hFF);
  cover property (@(comb_ev) dut.in == 8'h00);
  cover property (@(comb_ev) dut.in == 8'hAA);
  cover property (@(comb_ev) dut.in == 8'h55);

endmodule

bind priority_encoder_mux priority_encoder_mux_sva sva_inst(.dut(this));