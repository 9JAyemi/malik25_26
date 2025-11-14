// SVA for lc3_pipeline_stage4
module lc3_pipeline_stage4_sva(
  input        reset,
  input        clk,
  input        stall,
  input  [5:0] state,

  input  [19:0] I_DR,
  input  [1:0]  I_WBtype,
  input  [2:0]  I_Memtype,
  input  [15:0] I_Res,

  input  [19:0] O_DR,
  input  [1:0]  O_WBtype,
  input  [15:0] O_Res,

  input  [15:0] memdata,
  input  [15:0] memaddr,
  input         memtype,
  input  [15:0] memdatawr,
  input         memapply,

  input  [2:0]  CC,
  input         inst_ld
);

  default clocking cb @(negedge clk); endclocking
  default disable iff (reset);

  // Pipeline capture on ~stall (registered at negedge)
  assert property (!stall |=> O_DR     == $past(I_DR));
  assert property (!stall |=> O_WBtype == $past(I_WBtype));
  assert property (!stall |=> memaddr  == $past(I_Res));
  assert property (!stall |=> memtype  == $past(I_Memtype[0]));

  // Hold on stall
  assert property (stall |=> $stable({O_DR,O_WBtype,memtype,memaddr}));

  // Combinational invariants
  assert property (memdatawr == O_DR[15:0]);
  assert property (O_Res == ((memapply && !memtype) ? memdata : memaddr));

  // Mem control relationships
  assert property (memapply |-> state[4]);
  assert property (inst_ld  |-> !memtype);
  assert property ((memapply && !memtype) <-> (inst_ld && state[4]));

  // CC correctness from memdata
  assert property (memdata == 16'h0000          |-> CC == 3'b010);
  assert property (memdata != 16'h0000 &&  memdata[15] |-> CC == 3'b100);
  assert property (memdata != 16'h0000 && !memdata[15] |-> CC == 3'b001);

  // Useful coverage
  cover property (!stall ##1 O_DR == $past(I_DR));
  cover property (stall ##1 stall ##1 !stall);                 // stall burst then advance
  cover property (state[4] && memapply && !memtype && inst_ld && (O_Res==memdata)); // load
  cover property (state[4] && memapply &&  memtype);           // store
  cover property (memdata==16'h0000 && CC==3'b010);
  cover property (memdata!=16'h0000 &&  memdata[15] && CC==3'b100);
  cover property (memdata!=16'h0000 && !memdata[15] && CC==3'b001);

endmodule

bind lc3_pipeline_stage4 lc3_pipeline_stage4_sva u_lc3_pipeline_stage4_sva (.*);