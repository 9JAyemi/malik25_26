// SVA for instdec. Bind this module to the DUT and connect a sampling clk and rst_n.

module instdec_sva
(
  input  logic         clk,
  input  logic         rst_n,

  // DUT ports
  input  logic [31:0]  cae_inst,
  input  logic [63:0]  cae_data,
  input  logic         cae_inst_vld,

  input  logic         inst_val,
  input  logic [4:0]   inst_caep,
  input  logic         inst_aeg_wr,
  input  logic         inst_aeg_rd,
  input  logic [17:0]  inst_aeg_idx,
  input  logic         err_unimpl
);

  // Decode helpers
  logic top_1101x, top_11100, top_11101, top_11110;
  assign top_1101x = (cae_inst[28:25] == 4'b1101);
  assign top_11100 = (cae_inst[28:24] == 5'b11100);
  assign top_11101 = (cae_inst[28:24] == 5'b11101);
  assign top_11110 = (cae_inst[28:24] == 5'b11110);

  logic sub_1101x_40, sub_1101x_68, sub_1101x_70;
  assign sub_1101x_40 = top_1101x && (cae_inst[24:18] == 7'h40);
  assign sub_1101x_68 = top_1101x && (cae_inst[24:18] == 7'h68);
  assign sub_1101x_70 = top_1101x && (cae_inst[24:18] == 7'h70);

  logic sub_11100_18, sub_11100_20;
  assign sub_11100_18 = top_11100 && (cae_inst[23:18] == 6'h18);
  assign sub_11100_20 = top_11100 && (cae_inst[23:18] == 6'h20);

  logic sub_11101_1c;
  assign sub_11101_1c = top_11101 && (cae_inst[23:18] == 6'h1c);

  logic sub_11110_val, sub_11110_unimpl;
  assign sub_11110_val    = top_11110 && cae_inst[23];
  assign sub_11110_unimpl = top_11110 && !cae_inst[23];

  logic legal_impl;
  assign legal_impl = sub_1101x_40 | sub_1101x_68 | sub_1101x_70
                    | sub_11100_18 | sub_11100_20
                    | sub_11101_1c | sub_11110_val;

  // Expected outputs
  logic         exp_val, exp_wr, exp_rd, exp_unimpl;
  logic [4:0]   exp_caep;
  logic [17:0]  exp_idx;

  always_comb begin
    exp_val     = cae_inst_vld && sub_11110_val;
    exp_wr      = cae_inst_vld && (sub_1101x_40 | sub_11100_18 | sub_11100_20);
    exp_rd      = cae_inst_vld && (sub_1101x_68 | sub_1101x_70 | sub_11101_1c);
    exp_unimpl  = cae_inst_vld && !legal_impl;
    exp_caep    = top_11110 ? cae_inst[22:18] : 5'b0;

    unique case (1'b1)
      sub_1101x_40: exp_idx = cae_inst[17:0];
      sub_1101x_68: exp_idx = cae_data[17:0];
      sub_1101x_70: exp_idx = {6'b0, cae_inst[17:6]};
      sub_11100_18: exp_idx = {6'b0, cae_inst[17:12], cae_inst[5:0]};
      sub_11100_20: exp_idx = {6'b0, cae_inst[17:12], cae_inst[5:0]};
      sub_11101_1c: exp_idx = {6'b0, cae_inst[17:6]};
      default:      exp_idx = 18'b0;
    endcase
  end

  // Assertions
  property p_eq(a,b); @(posedge clk) disable iff (!rst_n) a == b; endproperty

  a_inst_val_eq:     assert property (p_eq(inst_val,    exp_val));
  a_inst_caep_eq:    assert property (p_eq(inst_caep,   exp_caep));
  a_inst_wr_eq:      assert property (p_eq(inst_aeg_wr, exp_wr));
  a_inst_rd_eq:      assert property (p_eq(inst_aeg_rd, exp_rd));
  a_err_unimpl_eq:   assert property (p_eq(err_unimpl,  exp_unimpl));
  a_idx_eq:          assert property (p_eq(inst_aeg_idx,exp_idx));

  // One-hot of action flags when valid; all zero when not valid
  a_onehot_when_vld: assert property (@(posedge clk) disable iff (!rst_n)
                                      cae_inst_vld |-> $onehot({inst_val,inst_aeg_wr,inst_aeg_rd,err_unimpl}));
  a_zero_when_not_vld: assert property (@(posedge clk) disable iff (!rst_n)
                                        !cae_inst_vld |-> !(inst_val|inst_aeg_wr|inst_aeg_rd|err_unimpl));

  // Mutual exclusion of rd/wr always
  a_wr_rd_mutex:     assert property (@(posedge clk) disable iff (!rst_n)
                                      !(inst_aeg_wr && inst_aeg_rd));

  // CAEP present only for 11110 decode
  a_caep_zero_else:  assert property (@(posedge clk) disable iff (!rst_n)
                                      !top_11110 |-> (inst_caep == 5'b0));

  // Coverage
  c_1101x_40_wr:     cover property (@(posedge clk) disable iff (!rst_n)
                                     cae_inst_vld && sub_1101x_40 && inst_aeg_wr && inst_aeg_idx==cae_inst[17:0]);
  c_1101x_68_rd:     cover property (@(posedge clk) disable iff (!rst_n)
                                     cae_inst_vld && sub_1101x_68 && inst_aeg_rd && inst_aeg_idx==cae_data[17:0]);
  c_1101x_70_rd:     cover property (@(posedge clk) disable iff (!rst_n)
                                     cae_inst_vld && sub_1101x_70 && inst_aeg_rd && inst_aeg_idx=={6'b0,cae_inst[17:6]});

  c_11100_18_wr:     cover property (@(posedge clk) disable iff (!rst_n)
                                     cae_inst_vld && sub_11100_18 && inst_aeg_wr && inst_aeg_idx=={6'b0,cae_inst[17:12],cae_inst[5:0]});
  c_11100_20_wr:     cover property (@(posedge clk) disable iff (!rst_n)
                                     cae_inst_vld && sub_11100_20 && inst_aeg_wr && inst_aeg_idx=={6'b0,cae_inst[17:12],cae_inst[5:0]});

  c_11101_1c_rd:     cover property (@(posedge clk) disable iff (!rst_n)
                                     cae_inst_vld && sub_11101_1c && inst_aeg_rd && inst_aeg_idx=={6'b0,cae_inst[17:6]});

  c_11110_val:       cover property (@(posedge clk) disable iff (!rst_n)
                                     cae_inst_vld && sub_11110_val && inst_val && (inst_caep==cae_inst[22:18]));
  c_11110_unimpl:    cover property (@(posedge clk) disable iff (!rst_n)
                                     cae_inst_vld && sub_11110_unimpl && err_unimpl);

  c_1101x_default:   cover property (@(posedge clk) disable iff (!rst_n)
                                     cae_inst_vld && top_1101x && !(sub_1101x_40|sub_1101x_68|sub_1101x_70) && err_unimpl);
  c_11100_default:   cover property (@(posedge clk) disable iff (!rst_n)
                                     cae_inst_vld && top_11100 && !(sub_11100_18|sub_11100_20) && err_unimpl);
  c_11101_default:   cover property (@(posedge clk) disable iff (!rst_n)
                                     cae_inst_vld && top_11101 && !sub_11101_1c && err_unimpl);
  c_top_default:     cover property (@(posedge clk) disable iff (!rst_n)
                                     cae_inst_vld && !(top_1101x|top_11100|top_11101|top_11110) && err_unimpl);

  // Optional: observe CAEP when vld=0
  c_caep_when_not_vld: cover property (@(posedge clk) disable iff (!rst_n)
                                       !cae_inst_vld && top_11110 && (inst_caep==cae_inst[22:18]) && !(inst_val|inst_aeg_wr|inst_aeg_rd|err_unimpl));

endmodule

// Example bind (replace tb_clk/tb_rst_n with your env clock/reset)
// bind instdec instdec_sva sva_inst ( .clk(tb_clk), .rst_n(tb_rst_n),
//   .cae_inst(cae_inst), .cae_data(cae_data), .cae_inst_vld(cae_inst_vld),
//   .inst_val(inst_val), .inst_caep(inst_caep), .inst_aeg_wr(inst_aeg_wr),
//   .inst_aeg_rd(inst_aeg_rd), .inst_aeg_idx(inst_aeg_idx), .err_unimpl(err_unimpl) );