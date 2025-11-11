// SVA for PCIeGen2x8If128_gtp_pipe_drp
// Bind into the DUT so we can reference internal regs and params
bind PCIeGen2x8If128_gtp_pipe_drp PCIeGen2x8If128_gtp_pipe_drp_sva();

module PCIeGen2x8If128_gtp_pipe_drp_sva;

  // Default clock/disable
  default clocking cb @(posedge DRP_CLK); endclocking
  default disable iff (!DRP_RST_N);

  // Basic state-space sanity
  assert property (fsm inside {FSM_IDLE,FSM_LOAD,FSM_READ,FSM_RRDY,FSM_WRITE,FSM_WRDY,FSM_DONE});
  assert property (index <= INDEX_MAX);

  // Output protocol equivalences
  assert property (DRP_EN == (fsm==FSM_READ || fsm==FSM_WRITE));
  assert property (DRP_WE == (fsm==FSM_WRITE));
  assert property (DRP_WE |-> DRP_EN);

  // Reset values (checked even during reset)
  property p_reset_values;
    @(posedge DRP_CLK)
      !DRP_RST_N |-> (
        x16_reg1==1'b0 && do_reg1==16'h0 && rdy_reg1==1'b0 && start_reg1==1'b0 &&
        x16_reg2==1'b0 && do_reg2==16'h0 && rdy_reg2==1'b0 && start_reg2==1'b0 &&
        load_cnt==2'd0 && index==5'd0 && addr_reg==9'd0 && di_reg==16'h0 &&
        fsm==FSM_IDLE && done==1'b1
      );
  endproperty
  assert property (p_reset_values);

  // Two-stage input pipeline behavior
  assert property (x16_reg1   == $past(DRP_X16));
  assert property (do_reg1    == $past(DRP_DO));
  assert property (rdy_reg1   == $past(DRP_RDY));
  assert property (start_reg1 == $past(DRP_START));

  assert property (x16_reg2   == $past(x16_reg1));
  assert property (do_reg2    == $past(do_reg1));
  assert property (rdy_reg2   == $past(rdy_reg1));
  assert property (start_reg2 == $past(start_reg1));

  // Address/data programming for index 0
  assert property (index==5'd0 |->
                   addr_reg==ADDR_RX_DATAWIDTH &&
                   di_reg == ((do_reg2 & MASK_RX_DATAWIDTH) | (x16_reg2 ? X16_RX_DATAWIDTH : X20_RX_DATAWIDTH)));
  // Bit-level check of the programmed field
  assert property (index==5'd0 |-> di_reg[11] == ~x16_reg2);

  // Index stability in non-update states
  assert property ((fsm inside {FSM_LOAD,FSM_READ,FSM_RRDY,FSM_WRITE,FSM_WRDY}) |-> $stable(index));

  // load_cnt behavior
  assert property ((fsm!=FSM_LOAD) |=> load_cnt==2'd0);
  assert property (($past(fsm)==FSM_LOAD && $past(load_cnt)<LOAD_CNT_MAX && fsm==FSM_LOAD)
                   |-> load_cnt==$past(load_cnt)+1);
  assert property (($past(fsm)==FSM_LOAD && $past(load_cnt)==LOAD_CNT_MAX && fsm==FSM_LOAD)
                   |-> load_cnt==LOAD_CNT_MAX);

  // FSM transitions and done/index effects
  assert property (fsm==FSM_IDLE && start_reg2 |=> fsm==FSM_LOAD && index==5'd0 && done==1'b0);
  assert property (fsm==FSM_IDLE && !start_reg2 |=> fsm==FSM_IDLE && index==5'd0 && done==1'b1);

  assert property (fsm==FSM_LOAD && load_cnt<LOAD_CNT_MAX |=> fsm==FSM_LOAD && done==1'b0);
  assert property (fsm==FSM_LOAD && load_cnt==LOAD_CNT_MAX |=> fsm==FSM_READ && done==1'b0);

  assert property (fsm==FSM_READ |=> fsm==FSM_RRDY);
  assert property (fsm==FSM_RRDY && !rdy_reg2 |=> fsm==FSM_RRDY);
  assert property (fsm==FSM_RRDY &&  rdy_reg2 |=> fsm==FSM_WRITE);

  assert property (fsm==FSM_WRITE |=> fsm==FSM_WRDY);
  assert property (fsm==FSM_WRDY && !rdy_reg2 |=> fsm==FSM_WRDY);
  assert property (fsm==FSM_WRDY &&  rdy_reg2 |=> fsm==FSM_DONE);

  assert property (fsm==FSM_DONE && index==INDEX_MAX |=> fsm==FSM_IDLE && index==5'd0 && done==1'b1);
  assert property (fsm==FSM_DONE && index< INDEX_MAX |=> fsm==FSM_LOAD && index==$past(index)+5'd1 && done==1'b0);

  // done semantics
  assert property (done == ((fsm==FSM_IDLE) || (fsm==FSM_DONE && index==INDEX_MAX)));

  // Coverage: one full successful transaction (needs two rdy pulses)
  cover property (
    start_reg2 ##1
    fsm==FSM_LOAD ##[1:$]
    fsm==FSM_READ ##1
    fsm==FSM_RRDY ##[1:$] (fsm==FSM_RRDY && rdy_reg2) ##1
    fsm==FSM_WRITE ##1
    fsm==FSM_WRDY ##[1:$] (fsm==FSM_WRDY && rdy_reg2) ##1
    fsm==FSM_DONE ##1
    fsm==FSM_IDLE && done
  );

  // Coverage: both X16/X20 programming observed at index 0
  cover property (index==5'd0 && x16_reg2==1'b1 && di_reg[11]==1'b0);
  cover property (index==5'd0 && x16_reg2==1'b0 && di_reg[11]==1'b1);

  // Coverage: load_cnt reaches saturation in LOAD
  cover property (fsm==FSM_LOAD ##[1:$] (fsm==FSM_LOAD && load_cnt==LOAD_CNT_MAX));

  // Coverage: index increment path when supported by parameter
  generate if (INDEX_MAX > 0) begin
    cover property (fsm==FSM_DONE && index<INDEX_MAX ##1 fsm==FSM_LOAD && index==$past(index)+5'd1);
  end endgenerate

endmodule