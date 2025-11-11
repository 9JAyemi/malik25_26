// SVA for timer_module
// Bindable checker with concise, high-value properties

module timer_module_sva (
  input  logic        clk,
  input  logic        reset,
  input  logic        wr,
  input  logic        tlo,
  input  logic        thi,
  input  logic        tcr,
  input  logic        count_en,
  input  logic [7:0]  data_in,
  input  logic [15:0] load_val,
  input  logic [7:0]  data_out,
  input  logic        tmra_ovf,
  input  logic        spmode,
  input  logic        irq,
  input  logic [15:0] count_val,

  // internal DUT signals
  input  logic [15:0] tmr,
  input  logic [7:0]  tmlh,
  input  logic [7:0]  tmll,
  input  logic [6:0]  tmcr,
  input  logic        forceload,
  input  logic        thi_load,
  input  logic        oneshot,
  input  logic        start,
  input  logic        reload,
  input  logic        zero,
  input  logic        underflow,
  input  logic        count
);

  default clocking cb @(posedge clk); endclocking
  default disable iff (reset);

  // Environment assumptions (single select)
  assume property (wr  |-> $onehot0({tlo,thi,tcr}));
  assume property (~wr |-> $onehot0({tlo,thi,tcr}));

  // Alias/decoding correctness
  assert property (count    == count_en);
  assert property (spmode   == tmcr[6]);
  assert property (oneshot  == tmcr[3]);
  assert property (start    == tmcr[0]);
  assert property (tmcr[4]  == 1'b0);         // strobe bit always 0
  assert property (zero     == ~|tmr);
  assert property (underflow== (zero && start && count));
  assert property (tmra_ovf == underflow);
  assert property (irq      == underflow);
  assert property (reload   == (thi_load || forceload || underflow));
  assert property (count_val== tmr);

  // Reset effects (synchronous)
  assert property (@(posedge clk) reset |=> tmcr == 7'd0);
  assert property (@(posedge clk) reset |=> tmr  == 16'hFFFF);
  assert property (@(posedge clk) reset |=> (tmll == 8'hFF && tmlh == 8'hFF));

  // Control register behavior
  assert property ((tcr && wr) |=> tmcr == {data_in[6:5],1'b0,data_in[3:0]});
  assert property ((thi_load && oneshot)  |=> tmcr[0] == 1'b1); // auto-start in oneshot after THI write
  assert property ((underflow && oneshot) |=> tmcr[0] == 1'b0); // auto-stop in oneshot at underflow

  // Strobes/loads
  assert property (forceload == $past(tcr && wr && data_in[4]));
  assert property (thi_load  == $past(thi && wr && (~start || oneshot)));

  // Counter update priority and function
  assert property (reload |=> tmr == $past(load_val));
  assert property ((start && count && !reload) |=> tmr == $past(tmr) - 16'd1);
  assert property ((!reload && !(start && count)) |=> tmr == $past(tmr));
  assert property (($past(tmr)==16'd0 && $past(start) && $past(count)) |-> (underflow && tmr == load_val));

  // Latches only change on write or reset
  assert property ((tlo && wr) |=> tmll == $past(data_in));
  assert property ((thi && wr) |=> tmlh == $past(data_in));
  assert property (!(tlo && wr) |=> tmll == $past(tmll));
  assert property (!(thi && wr) |=> tmlh == $past(tmlh));

  // Read mux correctness
  assert property ((~wr && tlo && !thi && !tcr) |-> data_out == tmr[7:0]);
  assert property ((~wr && thi && !tlo && !tcr) |-> data_out == tmr[15:8]);
  assert property ((~wr && tcr && !tlo && !thi) |-> data_out == {1'b0,tmcr});

  // Key coverage
  cover property (reset ##1 !reset);
  cover property ((tcr && wr) ##1 oneshot);
  cover property ((thi && wr && oneshot) ##1 thi_load ##1 reload);
  cover property ((tcr && wr && data_in[4]) ##1 forceload ##1 reload);
  cover property ((start && count && !reload)[*5]); // run for 5 cycles
  cover property (($past(tmr)==16'd0 && $past(start) && $past(count)) ##1 underflow);

endmodule

// Bind example:
// bind timer_module timer_module_sva sva_i (.*,
//   .tmr(tmr), .tmlh(tmlh), .tmll(tmll), .tmcr(tmcr), .forceload(forceload),
//   .thi_load(thi_load), .oneshot(oneshot), .start(start), .reload(reload),
//   .zero(zero), .underflow(underflow), .count(count)
// );