// SVA for stratixv_output_alignment
// Bind into DUT to access internals and parameters

module sva_stratixv_output_alignment (
  input  logic        clk,
  input  logic        areset,
  input  logic        sreset,
  input  logic        datain,
  input  logic        dffin,
  input  logic        dff1t,
  input  logic        dff2t,
  input  logic        dffphasetransfer,
  input  logic        dataout,
  input  logic [2:0]  enaoutputcycledelay,

  // internal state
  input  logic [2:0]  delay_counter,
  input  logic [2:0]  phase_transfer_counter,
  input  logic        delayed_data,
  input  logic        dff1t_reg,
  input  logic        dff2t_reg1,
  input  logic        dff2t_reg2,
  input  logic        dffphasetransfer_reg,

  // parameters as constants
  input  logic        aod, // add_output_cycle_delay
  input  logic        apr  // add_phase_transfer_reg
);

  default clocking cb @(posedge clk); endclocking

  // Basic sanity / wiring
  ap_no_x:                assert property ( !$isunknown({areset,datain,dffin,dff1t,dff2t,dffphasetransfer,dataout}) );
  ap_dffin_wiring:        assert property ( dffin == datain );
  ap_dff1t_wiring:        assert property ( dff1t == dff1t_reg );
  ap_dff2t_wiring:        assert property ( dff2t == (dff2t_reg1 & dff2t_reg2) );
  ap_dff2t_regs_equal:    assert property ( disable iff(!areset) dff2t_reg1 == dff2t_reg2 );
  ap_dffpt_wiring:        assert property ( dffphasetransfer == dffphasetransfer_reg );
  ap_dataout_wiring:      assert property ( dataout == delayed_data );

  // Asynchronous reset drives all state/outputs low while asserted
  ap_reset_outputs_zero:  assert property ( !areset |-> (dataout==1'b0 && dff1t==1'b0 && dff2t==1'b0 && dffphasetransfer==1'b0) );
  ap_reset_state_zero:    assert property ( !areset |-> (delay_counter==3'd0 && phase_transfer_counter==3'd0 &&
                                                         delayed_data==1'b0 && dff1t_reg==1'b0 &&
                                                         dff2t_reg1==1'b0 && dff2t_reg2==1'b0 && dffphasetransfer_reg==1'b0) );

  // Simple pipeline latencies
  ap_dff1t_latency:       assert property ( disable iff(!areset) dff1t == $past(datain) );
  ap_dff2t_from_dff1t:    assert property ( disable iff(!areset) dff2t == $past(dff1t) );
  ap_dff2t_from_datain:   assert property ( disable iff(!areset) dff2t == $past(datain,2) );
  ap_dff2t_one_implies_prev1: assert property ( disable iff(!areset) dff2t |-> $past(dff1t) );

  // Phase transfer counter behavior
  ap_pt_cnt_hold_when_off: assert property ( disable iff(!areset) !apr |-> phase_transfer_counter == $past(phase_transfer_counter) );
  ap_pt_cnt_counts:        assert property ( disable iff(!areset) apr |-> phase_transfer_counter ==
                                             (($past(phase_transfer_counter)==3'd7) ? 3'd0 : $past(phase_transfer_counter)+3'd1) );

  // dffphasetransfer update policy
  ap_pt_noextra_delay:     assert property ( disable iff(!areset) !apr |-> dffphasetransfer == $past(datain) );
  ap_pt_sample_on_zero:    assert property ( disable iff(!areset) (apr && ($past(phase_transfer_counter)==3'd0)) |-> dffphasetransfer == $past(datain) );
  ap_pt_hold_else:         assert property ( disable iff(!areset) (apr && ($past(phase_transfer_counter)!=3'd0)) |-> dffphasetransfer == $past(dffphasetransfer) );

  // Output cycle delay counter behavior
  ap_od_cnt_hold_when_off: assert property ( disable iff(!areset) !aod |-> delay_counter == $past(delay_counter) );
  ap_od_cnt_counts:        assert property ( disable iff(!areset) aod |-> delay_counter ==
                                             (($past(delay_counter)==$past(enaoutputcycledelay)) ? 3'd0 : $past(delay_counter)+3'd1) );

  // dataout update policy
  ap_od_no_delay:          assert property ( disable iff(!areset) !aod |-> dataout == $past(dffphasetransfer) );
  ap_od_update_on_match:   assert property ( disable iff(!areset) (aod && ($past(delay_counter)==$past(enaoutputcycledelay))) |-> dataout == $past(dffphasetransfer) );
  ap_od_hold_else:         assert property ( disable iff(!areset) (aod && ($past(delay_counter)!=$past(enaoutputcycledelay))) |-> dataout == $past(dataout) );

  // End-to-end in the simplest mode (both features off): total 2-cycle latency
  ap_e2e_min_mode:         assert property ( disable iff(!areset) (!apr && !aod) |-> dataout == $past(datain,2) );

  // Coverage
  cp_reset_deassert:       cover property ( $rose(areset) );
  cp_reset_assert:         cover property ( $fell(areset) );

  cp_data_pipeline:        cover property ( disable iff(!areset)
                                (datain != $past(datain)) ##1 (dff1t == $past(datain)) ##1 (dff2t == $past(datain)) );

  cp_pt_update:            cover property ( disable iff(!areset) apr && (phase_transfer_counter==3'd0)
                                ##1 (dffphasetransfer != $past(dffphasetransfer)) );

  cp_od_update_any:        cover property ( disable iff(!areset) aod && (delay_counter==enaoutputcycledelay)
                                ##1 (dataout != $past(dataout)) );

  cp_od_update_e0:         cover property ( disable iff(!areset) aod && (enaoutputcycledelay==3'd0) && (delay_counter==3'd0)
                                ##1 (dataout == $past(dffphasetransfer)) );

  cp_od_update_e7:         cover property ( disable iff(!areset) aod && (enaoutputcycledelay==3'd7) && (delay_counter==3'd7)
                                ##1 (dataout == $past(dffphasetransfer)) );

  cp_sreset_seen:          cover property ( $changed(sreset) );

endmodule

bind stratixv_output_alignment sva_stratixv_output_alignment u_sva_stratixv_output_alignment (
  .clk                     (clk),
  .areset                  (areset),
  .sreset                  (sreset),
  .datain                  (datain),
  .dffin                   (dffin),
  .dff1t                   (dff1t),
  .dff2t                   (dff2t),
  .dffphasetransfer        (dffphasetransfer),
  .dataout                 (dataout),
  .enaoutputcycledelay     (enaoutputcycledelay),

  .delay_counter           (delay_counter),
  .phase_transfer_counter  (phase_transfer_counter),
  .delayed_data            (delayed_data),
  .dff1t_reg               (dff1t_reg),
  .dff2t_reg1              (dff2t_reg1),
  .dff2t_reg2              (dff2t_reg2),
  .dffphasetransfer_reg    (dffphasetransfer_reg),

  .aod                     (add_output_cycle_delay),
  .apr                     (add_phase_transfer_reg)
);