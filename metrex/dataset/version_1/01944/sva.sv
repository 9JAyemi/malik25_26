// SVA for ID_EX. Bind this checker to the DUT.
// Focus: async reset behavior, stall hold behavior, pass-through when running, and basic coverage.

module ID_EX_sva (
  input  logic        clk, rst, stall,
  input  logic [31:0] id_a, id_b, id_d2, id_instr, id_pc,
  input  logic [4:0]  id_td, id_Aluc,
  input  logic        id_WREG, id_WMEM, id_LW,
  input  logic [31:0] ex_a, ex_b, ex_d2, ex_instr, ex_pc,
  input  logic [4:0]  ex_td, ex_Aluc,
  input  logic        ex_WREG, ex_WMEM, ex_LW
);

  // Default clock for assertions
  default clocking cb @(posedge clk); endclocking

  // Async reset drives known reset values immediately
  property p_async_reset;
    @(posedge rst)
      1 |-> (ex_a==32'b0 && ex_b==32'b0 && ex_d2==32'b0 &&
             ex_td==5'b0 && ex_Aluc==5'b0 &&
             ex_WREG==1'b0 && ex_WMEM==1'b0 && ex_LW==1'b0 &&
             ex_instr==32'b100000 && ex_pc==32'b0);
  endproperty
  assert property (p_async_reset)
    else $error("ID_EX: async reset values mismatch");

  // While reset is asserted, hold reset values
  property p_hold_during_reset;
    rst |-> (ex_a==32'b0 && ex_b==32'b0 && ex_d2==32'b0 &&
             ex_td==5'b0 && ex_Aluc==5'b0 &&
             ex_WREG==1'b0 && ex_WMEM==1'b0 && ex_LW==1'b0 &&
             ex_instr==32'b100000 && ex_pc==32'b0);
  endproperty
  assert property (p_hold_during_reset)
    else $error("ID_EX: outputs not held at reset values while rst asserted");

  // When not in reset, ex_instr/ex_pc always follow inputs (both when stalled and running)
  property p_instr_pc_follow;
    disable iff (rst)
      1 |-> (ex_instr==id_instr && ex_pc==id_pc);
  endproperty
  assert property (p_instr_pc_follow)
    else $error("ID_EX: ex_instr/ex_pc must mirror id_instr/id_pc when not in reset");

  // Running (stall=0): all other outputs mirror inputs at the clock edge
  property p_run_pass_through;
    disable iff (rst)
      (!stall) |-> ({ex_a,ex_b,ex_d2,ex_td,ex_Aluc,ex_WREG,ex_WMEM,ex_LW}
                   =={id_a, id_b, id_d2, id_td, id_Aluc, id_WREG, id_WMEM, id_LW});
  endproperty
  assert property (p_run_pass_through)
    else $error("ID_EX: pass-through mismatch when not stalled");

  // Stalled (stall=1): hold previous values for all except instr/pc
  property p_stall_holds_others;
    disable iff (rst)
      stall |-> ({ex_a,ex_b,ex_d2,ex_td,ex_Aluc,ex_WREG,ex_WMEM,ex_LW}
                ==$past({ex_a,ex_b,ex_d2,ex_td,ex_Aluc,ex_WREG,ex_WMEM,ex_LW}));
  endproperty
  assert property (p_stall_holds_others)
    else $error("ID_EX: outputs did not hold during stall");

  // Basic functional coverage
  cover property (@(posedge rst) 1);                                 // saw async reset
  cover property (disable iff (rst) (!stall));                        // ran (not stalled)
  cover property (disable iff (rst) (stall));                         // stalled
  cover property (disable iff (rst) (!stall ##1 stall ##1 !stall));   // run->stall->run sequence
  cover property (disable iff (rst) (stall ##1 stall));               // multi-cycle stall

endmodule

// Bind to DUT
bind ID_EX ID_EX_sva ID_EX_sva_i (
  .clk(clk), .rst(rst), .stall(stall),
  .id_a(id_a), .id_b(id_b), .id_d2(id_d2), .id_instr(id_instr), .id_pc(id_pc),
  .id_td(id_td), .id_Aluc(id_Aluc), .id_WREG(id_WREG), .id_WMEM(id_WMEM), .id_LW(id_LW),
  .ex_a(ex_a), .ex_b(ex_b), .ex_d2(ex_d2), .ex_instr(ex_instr), .ex_pc(ex_pc),
  .ex_td(ex_td), .ex_Aluc(ex_Aluc), .ex_WREG(ex_WREG), .ex_WMEM(ex_WMEM), .ex_LW(ex_LW)
);