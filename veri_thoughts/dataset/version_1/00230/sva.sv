// SVA for ad_datafmt: concise, high-quality checks and key coverage
// Bind as: bind ad_datafmt ad_datafmt_sva #(.DATA_WIDTH(DATA_WIDTH), .DISABLE(DISABLE)) sva_i(.*);

module ad_datafmt_sva #(
  parameter int DATA_WIDTH = 16,
  parameter int DISABLE    = 0
) (ad_datafmt dut);

  // Basic parameter sanity (static)
  initial begin
    assert (DATA_WIDTH >= 1 && DATA_WIDTH <= 16)
      else $error("ad_datafmt: DATA_WIDTH must be 1..16 (got %0d)", DATA_WIDTH);
  end

  default clocking cb @(posedge dut.clk); endclocking

  // Golden model of combinational formatter (16-bit)
  function automatic logic [15:0] fmt16(input logic [DATA_WIDTH-1:0] d,
                                        input logic en, t, se);
    logic type_s, msb, upper;
    logic [15:0] r;
    type_s = en & t;
    msb    = d[DATA_WIDTH-1] ^ type_s;
    r      = '0;
    if (DATA_WIDTH > 1) r[DATA_WIDTH-2:0] = d[DATA_WIDTH-2:0];
    r[DATA_WIDTH-1] = msb;
    if (DATA_WIDTH < 16) begin
      upper = (en & se) & msb;
      r[15:DATA_WIDTH] = {(16-DATA_WIDTH){upper}};
    end
    return r;
  endfunction

  // Behavior checks
  if (DISABLE) begin : g_disable_checks
    // Pure passthrough (combinational) — sampled on clk for SVA
    ap_ps_v: assert property (dut.valid_out == dut.valid)
      else $error("DISABLE: valid_out != valid");
    ap_ps_d: assert property (dut.data_out == { {(16-DATA_WIDTH){1'b0}}, dut.data })
      else $error("DISABLE: data_out != zero-extended data");
  end else begin : g_pipe_checks
    // 1-cycle pipeline
    ap_p_v: assert property (dut.valid_out == $past(dut.valid,1,1'b0))
      else $error("PIPE: valid_out not 1-cycle delayed");
    ap_p_d: assert property (
               dut.data_out ==
               $past(fmt16(dut.data, dut.dfmt_enable, dut.dfmt_type, dut.dfmt_se), 1, 16'h0)
             )
      else $error("PIPE: data_out not equal to formatted $past(data,ctrl)");
  end

  // Key functional coverage
  if (!DISABLE) begin : g_cov
    // Pipeline activity
    cp_v_pipe:    cover property (dut.valid ##1 dut.valid_out);

    // Pass-through mode (dfmt_enable=0)
    cp_passthru:  cover property (!dut.dfmt_enable);

    // Invert MSB only (enable & type, no sign-extend), both MSB polarities
    cp_inv_msb0:  cover property (dut.dfmt_enable && dut.dfmt_type && !dut.dfmt_se && (dut.data[DATA_WIDTH-1]==1'b0));
    cp_inv_msb1:  cover property (dut.dfmt_enable && dut.dfmt_type && !dut.dfmt_se && (dut.data[DATA_WIDTH-1]==1'b1));

    // Sign-extend path exercised for both MSB polarities
    if (DATA_WIDTH < 16) begin
      cp_se_msb0: cover property (dut.dfmt_enable && dut.dfmt_se && (dut.data[DATA_WIDTH-1]==1'b0));
      cp_se_msb1: cover property (dut.dfmt_enable && dut.dfmt_se && (dut.data[DATA_WIDTH-1]==1'b1));
    end
  end else begin : g_cov_disable
    // Passthrough path toggles
    cp_ps_dchg: cover property ($changed(dut.data) |-> $changed(dut.data_out));
    cp_ps_vchg: cover property ($changed(dut.valid) |-> $changed(dut.valid_out));
  end

endmodule