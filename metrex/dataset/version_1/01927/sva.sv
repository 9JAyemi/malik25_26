// SVA for step_id: concise, high-quality checks and coverage
// Bind example (from testbench):
// bind step_id step_id_sva u_step_id_sva(.clk(tb_clk), .rst_n(tb_rst_n), .*);

module step_id_sva
(
  input  logic        clk,
  input  logic        rst_n,

  input  logic [7:0]  inst,
  input  logic        ena_,
  input  logic        cond_dout,

  input  logic        rdy_nop_, rdy_cpf_, rdy_cpt_, rdy_ld_, rdy_st_, rdy_clr_, rdy_im_, rdy_tce_, rdy_ts_, rdy_add_, rdy_sub_
);

  default clocking cb @(posedge clk); endclocking
  default disable iff (!rst_n);

  // Recompute expected decode
  logic        cond_;
  logic [6:0]  exp_inst_cond;

  logic exp_rdy_nop_, exp_rdy_cpf_, exp_rdy_cpt_, exp_rdy_ld_, exp_rdy_st_, exp_rdy_clr_, exp_rdy_im_, exp_rdy_tce_, exp_rdy_ts_, exp_rdy_add_, exp_rdy_sub_;

  always_comb begin
    cond_          = inst[7] ^ cond_dout;
    exp_inst_cond  = inst[6:0] & {7{~(cond_ | ena_)}};

    exp_rdy_nop_   = (exp_inst_cond != 7'b0000000) || ena_;
    exp_rdy_cpf_   = (exp_inst_cond[6:4] != 3'b010) || (exp_inst_cond[3:0] == 4'b0000);
    exp_rdy_cpt_   = (exp_inst_cond[6:4] != 3'b011) || (exp_inst_cond[3:0] == 4'b0000);
    exp_rdy_ld_    = ({exp_inst_cond[6:2], exp_inst_cond[0]} != {5'b10001, 1'b0});
    exp_rdy_st_    = ({exp_inst_cond[6:2], exp_inst_cond[0]} != {5'b10001, 1'b1});
    exp_rdy_clr_   = (exp_inst_cond != 7'b1010000);
    exp_rdy_im_    = (exp_inst_cond[6:5] != 2'b11);
    exp_rdy_tce_   = (exp_inst_cond != 7'b0001100);
    exp_rdy_ts_    = ({exp_inst_cond[6], exp_inst_cond[3:0]} != {1'b0, 4'b0000}) || (exp_inst_cond[5:4] == 2'b00);
    exp_rdy_add_   = (exp_inst_cond != 7'b1010110);
    exp_rdy_sub_   = (exp_inst_cond != 7'b1010111);
  end

  // Equivalence assertions (golden vs DUT)
  assert property (rdy_nop_ == exp_rdy_nop_);
  assert property (rdy_cpf_ == exp_rdy_cpf_);
  assert property (rdy_cpt_ == exp_rdy_cpt_);
  assert property (rdy_ld_  == exp_rdy_ld_);
  assert property (rdy_st_  == exp_rdy_st_);
  assert property (rdy_clr_ == exp_rdy_clr_);
  assert property (rdy_im_  == exp_rdy_im_);
  assert property (rdy_tce_ == exp_rdy_tce_);
  assert property (rdy_ts_  == exp_rdy_ts_);
  assert property (rdy_add_ == exp_rdy_add_);
  assert property (rdy_sub_ == exp_rdy_sub_);

  // X-propagation sanity: clean outputs when inputs are clean
  assert property (!$isunknown({inst, ena_, cond_dout}) |-> !$isunknown({rdy_nop_, rdy_cpf_, rdy_cpt_, rdy_ld_, rdy_st_, rdy_clr_, rdy_im_, rdy_tce_, rdy_ts_, rdy_add_, rdy_sub_}));

  // Gating behavior: when cond_ or ena_ asserted, all decodes deassert except rdy_nop_==ena_
  assert property ( (cond_ || ena_) |->
                    (rdy_nop_ == ena_) &&
                    rdy_cpf_ && rdy_cpt_ && rdy_ld_ && rdy_st_ && rdy_clr_ && rdy_im_ && rdy_tce_ && rdy_ts_ && rdy_add_ && rdy_sub_);

  // Mutual exclusivity of active-low decodes (at most one low)
  assert property ( $onehot0({~rdy_nop_, ~rdy_cpf_, ~rdy_cpt_, ~rdy_ld_, ~rdy_st_, ~rdy_clr_, ~rdy_im_, ~rdy_tce_, ~rdy_ts_, ~rdy_add_, ~rdy_sub_}) );

  // Strong pairwise disjointness for closely-related decoders
  assert property ( !(~rdy_ld_  && ~rdy_st_)  );
  assert property ( !(~rdy_cpf_ && ~rdy_cpt_) );
  assert property ( !(~rdy_add_ && ~rdy_sub_) );

  // Targeted covers (prove reachability of each decode)
  cover property (! (cond_ || ena_) && !rdy_nop_);        // NOP (conditional or true zero)
  cover property (! (cond_ || ena_) && !rdy_cpf_);
  cover property (! (cond_ || ena_) && !rdy_cpt_);
  cover property (! (cond_ || ena_) && !rdy_ld_);
  cover property (! (cond_ || ena_) && !rdy_st_);
  cover property (! (cond_ || ena_) && !rdy_clr_);
  cover property (! (cond_ || ena_) && !rdy_im_);
  cover property (! (cond_ || ena_) && !rdy_tce_);
  cover property (! (cond_ || ena_) && !rdy_ts_);
  cover property (! (cond_ || ena_) && !rdy_add_);
  cover property (! (cond_ || ena_) && !rdy_sub_);

  // Cover gating corners
  cover property (cond_ &&  ena_ && rdy_nop_);   // both high -> nop stays high
  cover property (cond_ && !ena_ && !rdy_nop_);  // failed condition acts as NOP
  cover property (!cond_ &&  ena_ && rdy_nop_);  // enable masks decode, nop==ena_

endmodule