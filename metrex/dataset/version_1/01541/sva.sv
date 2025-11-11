// SVA for ME_WB
module ME_WB_sva(
  input logic        clk,
  input logic        rst,
  input logic        stall,
  input logic [31:0] me_memdata,
  input logic [4:0]  me_td,
  input logic        me_WREG,
  input logic [31:0] wb_memdata,
  input logic [4:0]  wb_td,
  input logic        wb_WREG
);

  // While reset is asserted, outputs must be zero on every clock edge
  property p_reset_forces_zero;
    @(posedge clk) rst |-> (wb_memdata == '0 && wb_td == '0 && wb_WREG == 1'b0);
  endproperty
  assert property (p_reset_forces_zero);

  // Stall drives zeros next cycle
  property p_stall_zero_next;
    @(posedge clk) disable iff (rst)
      stall |=> (wb_memdata == '0 && wb_td == '0 && wb_WREG == 1'b0);
  endproperty
  assert property (p_stall_zero_next);

  // Pass-through in 1 cycle when not stalled
  property p_pass_through_1cycle;
    @(posedge clk) disable iff (rst)
      !stall |=> (wb_memdata == $past(me_memdata) &&
                  wb_td      == $past(me_td)      &&
                  wb_WREG    == $past(me_WREG));
  endproperty
  assert property (p_pass_through_1cycle);

  // No X/Z on outputs when not in reset
  property p_no_unknown_out;
    @(posedge clk) disable iff (rst)
      !$isunknown({wb_memdata, wb_td, wb_WREG});
  endproperty
  assert property (p_no_unknown_out);

  // Coverage
  cover property (@(posedge clk) $rose(rst));
  cover property (@(posedge clk) !rst && $rose(stall));
  cover property (@(posedge clk) !rst && !stall && $changed(me_memdata)
                  ##1 (wb_memdata == $past(me_memdata)));
  cover property (@(posedge clk) !rst && stall[*2]);

endmodule

bind ME_WB ME_WB_sva sva_inst(
  .clk(clk),
  .rst(rst),
  .stall(stall),
  .me_memdata(me_memdata),
  .me_td(me_td),
  .me_WREG(me_WREG),
  .wb_memdata(wb_memdata),
  .wb_td(wb_td),
  .wb_WREG(wb_WREG)
);