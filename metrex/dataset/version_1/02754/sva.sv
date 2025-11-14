// SVA checker for KEY2INST
module KEY2INST_sva;

  default clocking cb @(posedge clk); endclocking
  `define DISABLE disable iff (!rst_n)

  // 1) State encoding and validity
  assert property (`DISABLE $onehot(st));
  assert property (`DISABLE st inside {st_idle,st_load,st_run,st_wrom,st_reset});

  // 2) Reset behavior
  assert property (@(negedge rst_n) st == st_reset);
  assert property (@(posedge clk) !rst_n |-> st == st_reset);

  // 3) State transitions
  assert property (`DISABLE (st==st_idle && run && !load) |=> st==st_wrom);
  assert property (`DISABLE (st==st_idle && run &&  load) |=> st==st_wrom);
  assert property (`DISABLE (st==st_idle && !run && load) |=> st==st_load);
  assert property (`DISABLE (st==st_idle && !run && !load)|=> st==st_idle);
  assert property (`DISABLE (st==st_wrom)  |=> st==st_run);
  assert property (`DISABLE (st==st_reset) |=> st==st_idle);
  assert property (`DISABLE (st==st_load)  |=> st==st_idle);
  assert property (`DISABLE (st==st_run && run)  |=> st==st_run);
  assert property (`DISABLE (st==st_run && !run) |=> st==st_idle);

  // 4) clrn behavior
  assert property (`DISABLE (st==st_run)   |=> clrn==1'b1);
  assert property (`DISABLE (st==st_reset) |=> clrn==1'b0);
  assert property (`DISABLE (st==st_wrom)  |=> clrn==1'b0);

  // 5) cmd_do decode correctness
  assert property (`DISABLE (cmd==cmd_add) |-> cmd_do=={5'b00001,5'b00010,5'b00011,5'b0,func_add});
  assert property (`DISABLE (cmd==cmd_sub) |-> cmd_do=={5'b00001,5'b00010,5'b00011,5'b0,func_sub});
  assert property (`DISABLE (cmd==cmd_and) |-> cmd_do=={5'b00001,5'b00010,5'b00011,5'b0,func_and});
  assert property (`DISABLE (cmd==cmd_or)  |-> cmd_do=={5'b00001,5'b00010,5'b00011,5'b0,func_or});
  assert property (`DISABLE (cmd==cmd_xor) |-> cmd_do=={5'b00001,5'b00010,5'b00011,5'b0,func_xor});
  assert property (`DISABLE (cmd==cmd_sll) |-> cmd_do=={5'b0,5'b00001,5'b00011,data_now[3][4:0],func_sll});
  assert property (`DISABLE (cmd==cmd_srl) |-> cmd_do=={5'b0,5'b00001,5'b00011,data_now[3][4:0],func_srl});
  assert property (`DISABLE (cmd==cmd_sra) |-> cmd_do=={5'b0,5'b00001,5'b00011,data_now[3][4:0],func_sra});
  assert property (`DISABLE !$isunknown(cmd));

  // 6) data_now load behavior and reset clearing
  genvar gi;
  generate
    for (gi=0; gi<4; gi++) begin : g_dn
      assert property (`DISABLE (st==st_load && select==gi) |=> data_now[gi] == $past(data));
      assert property (`DISABLE (st==st_load && select!=gi) |=> data_now[gi] == $past(data_now[gi]));
      // ensure clear on st_reset
      assert property (           (st==st_reset)            |=> data_now[gi] == 8'h00);
    end
  endgenerate

  // 7) inst_rom writes during st_wrom (checked next cycle)
  assert property (`DISABLE (st==st_wrom) |=> inst_rom[0] == {6'b001000,5'b00000,5'b00001,$past(data_now[0]),$past(data_now[1])});
  assert property (`DISABLE (st==st_wrom) |=> inst_rom[1] == {6'b001000,5'b00000,5'b00010,$past(data_now[2]),$past(data_now[3])});
  assert property (`DISABLE (st==st_wrom) |=> inst_rom[2] == {6'b000000,$past(cmd_do)});
  assert property (`DISABLE (st==st_wrom) |=> inst_rom[3] == {6'b000010,26'd3});

  // 8) inst_do mapping to ROM
  assert property (`DISABLE inst_do == inst_rom[inst_a[6:2]]);

  // 9) X-check critical controls
  assert property (`DISABLE !$isunknown({rst_n,run,load,select,data,st,clrn}));

  // 10) Coverage
  // Full flow: idle -> load -> idle -> wrom -> run -> idle
  cover property (`DISABLE (st==st_idle && !run && load)
                  ##1 (st==st_load)
                  ##1 (st==st_idle)
                  ##1 (run)
                  ##1 (st==st_wrom)
                  ##1 (st==st_run)
                  ##1 (!run)
                  ##1 (st==st_idle));

  // Cover each cmd value seen
  genvar gc;
  generate for (gc=0; gc<8; gc++) begin : g_cmd_cov
    cover property (`DISABLE (cmd==gc[2:0]));
  end endgenerate

  // Cover each select used during load
  genvar gs;
  generate for (gs=0; gs<4; gs++) begin : g_sel_cov
    cover property (`DISABLE (st==st_load && select==gs));
  end endgenerate

  // Cover ROM write of instruction using current cmd_do
  cover property (`DISABLE (st==st_wrom) ##1 (inst_rom[2] == {6'b000000,$past(cmd_do)}));

endmodule

bind KEY2INST KEY2INST_sva u_KEY2INST_sva();