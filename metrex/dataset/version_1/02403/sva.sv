// SVA checker for EXMEMreg: 1-cycle pipeline register with no reset
// Bind this to the DUT. Focused, high-quality checks + minimal coverage.

module EXMEMreg_sva (
  input clk,
  input [4:0]  Rtin, Rdin,
  input [31:0] PCplusin, ALUresultin, DatabusBin,
  input [1:0]  RegDstin, MemtoRegin,
  input        RegWrin, MemWrin, MemRdin,
  input [4:0]  Rtout, Rdout,
  input [31:0] PCplusout, ALUresultout, DatabusBout,
  input [1:0]  RegDstout, MemtoRegout,
  input        RegWrout, MemWrout, MemRdout
);

  default clocking cb @(posedge clk); endclocking

  // Guard to avoid using $past on the first active clock
  logic past_valid;
  always @(posedge clk) past_valid <= 1'b1;

  // Concatenated buses for concise checks
  wire [112:0] ins_cat  = {Rtin,Rdin,PCplusin,ALUresultin,DatabusBin,RegDstin,RegWrin,MemWrin,MemRdin,MemtoRegin};
  wire [112:0] outs_cat = {Rtout,Rdout,PCplusout,ALUresultout,DatabusBout,RegDstout,RegWrout,MemWrout,MemRdout,MemtoRegout};

  // 1-cycle latency: all outputs equal previous-cycle inputs
  a_latency: assert property (past_valid |-> outs_cat == $past(ins_cat));

  // No spurious X on outputs when previous inputs were known
  a_known_if_known: assert property (past_valid && !$isunknown($past(ins_cat)) |-> !$isunknown(outs_cat));

  // No glitches between rising edges: outputs stable at negedge
  a_no_glitch: assert property (@(negedge clk) $stable(outs_cat));

  // Minimal but meaningful coverage: observe a change propagate through the register
  c_change_propagates: cover property (past_valid && $changed(ins_cat) ##1 outs_cat == $past(ins_cat));

  // Control bit toggles propagate (examples)
  c_RegWr_rise:  cover property (past_valid && $rose(RegWrin) ##1 RegWrout);
  c_MemWr_rise:  cover property (past_valid && $rose(MemWrin) ##1 MemWrout);
  c_MemRd_rise:  cover property (past_valid && $rose(MemRdin) ##1 MemRdout);

endmodule

// Bind to all instances of EXMEMreg
bind EXMEMreg EXMEMreg_sva EXMEMreg_sva_i (.*);