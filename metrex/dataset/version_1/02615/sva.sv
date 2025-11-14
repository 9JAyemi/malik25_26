// SVA for bcdtoseg. Bind this module to the DUT.
module bcdtoseg_sva (bcdtoseg dut);

  default clocking cb @($global_clock); endclocking

  // Pack convenience signals
  wire [3:0] segin = {dut.A3, dut.A2, dut.A1, dut.A0};
  wire [6:0] nout  = {dut.nA, dut.nB, dut.nC, dut.nD, dut.nE, dut.nF, dut.nG};

  // Expected decode (active-low outputs) in normal mode (nRBO=1, nLT=1)
  function automatic [6:0] exp_nout_norm (input [3:0] s);
    case (s)
      4'd0:  exp_nout_norm = ~7'b1111110;
      4'd1:  exp_nout_norm = ~7'b0110000;
      4'd2:  exp_nout_norm = ~7'b1101101;
      4'd3:  exp_nout_norm = ~7'b1111001;
      4'd4:  exp_nout_norm = ~7'b0110011;
      4'd5:  exp_nout_norm = ~7'b1011011;
      4'd6:  exp_nout_norm = ~7'b1011111;
      4'd7:  exp_nout_norm = ~7'b1110000;
      4'd8:  exp_nout_norm = ~7'b1111111;
      4'd9:  exp_nout_norm = ~7'b1111011;
      4'hF:  exp_nout_norm = ~7'b1100111;
      default: exp_nout_norm = ~7'b0000000; // blank for 10..14
    endcase
  endfunction

  // nRBO combinational equation equivalence
  ap_nRBO_eq: assert property (
    !$isunknown({dut.nLT, dut.nRBI, segin, dut.nBI}) |-> 
    (dut.nRBO == ~(~dut.nBI || (~dut.nRBI && (segin == 4'd0) && dut.nLT)))
  );

  // Blanking has highest priority
  ap_blank_on_nRBO: assert property (
    (dut.nRBO === 1'b0) |-> (nout === 7'b1111111)
  );

  // Lamp test (when not blanked)
  ap_lamp_test: assert property (
    (!$isunknown({dut.nRBO, dut.nLT}) && dut.nRBO && !dut.nLT) |-> (nout === 7'b0000000)
  );

  // Normal decode (when not blanked and LT inactive)
  ap_normal_decode: assert property (
    (!$isunknown({dut.nRBO, dut.nLT, segin}) && dut.nRBO && dut.nLT) |-> (nout === exp_nout_norm(segin))
  );

  // Coverage

  // Blanking via nBI
  cp_blank_via_nBI: cover property (dut.nBI == 1'b0 && dut.nRBO == 1'b0);

  // Blanking via nRBI with 0 input and LT high
  cp_blank_via_nRBI: cover property (dut.nRBI == 1'b0 && segin == 4'd0 && dut.nLT == 1'b1 && dut.nRBO == 1'b0);

  // Lamp test path observed
  cp_lamp_test: cover property (dut.nRBO == 1'b1 && dut.nLT == 1'b0 && nout == 7'b0000000);

  // Normal decode digits 0..9
  genvar i;
  generate
    for (i = 0; i <= 9; i++) begin : gen_cov_digits
      cover property (dut.nRBO && dut.nLT && segin == i[3:0] && nout == exp_nout_norm(i[3:0]));
    end
  endgenerate

  // Normal decode for F
  cp_F: cover property (dut.nRBO && dut.nLT && segin == 4'hF && nout == exp_nout_norm(4'hF));

  // Any invalid BCD (10..14) produces blank in normal mode
  cp_invalids: cover property (dut.nRBO && dut.nLT && (segin inside {4'd10,4'd11,4'd12,4'd13,4'd14}) && nout == 7'b1111111);

endmodule

// Bind to DUT
bind bcdtoseg bcdtoseg_sva sva_i();