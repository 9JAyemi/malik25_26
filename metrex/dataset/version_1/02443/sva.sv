// SVA for control_ascci
// Bind this module into the DUT:  bind control_ascci control_ascci_sva svas();

module control_ascci_sva;
  // Assumes binding into control_ascci scope (can directly see DUT signals/params)
  default clocking cb @(negedge clk); endclocking
  default disable iff ($isunknown(current_state));

  // Legal state
  assert property (current_state inside {start, state_1p, state_1, state_2, state_3, state_4, state_5, check});

  // Outputs fully specified and non-X in legal states
  assert property ((current_state inside {start, state_1p, state_1, state_2, state_3, state_4, state_5, check})
                   |-> !$isunknown({add_dirram,reset_dirram,add_col,reset_col,add_ascci,reset_ascci,leer_rom,leer_ram,init,run_efect}));

  // Moore output decode (concise vector: {add_dirram,reset_dirram,add_col,reset_col,add_ascci,reset_ascci,leer_rom,leer_ram,init,run_efect})
  assert property ((current_state==start)   |-> {add_dirram,reset_dirram,add_col,reset_col,add_ascci,reset_ascci,leer_rom,leer_ram,init,run_efect} == 10'b0_1_0_1_0_0_0_1_0_0);
  assert property ((current_state==state_1p)|-> {add_dirram,reset_dirram,add_col,reset_col,add_ascci,reset_ascci,leer_rom,leer_ram,init,run_efect} == 10'b0_0_0_0_0_1_1_0_1_0);
  assert property ((current_state==state_1) |-> {add_dirram,reset_dirram,add_col,reset_col,add_ascci,reset_ascci,leer_rom,leer_ram,init,run_efect} == 10'b0_0_0_0_0_0_1_0_1_0);
  assert property ((current_state==state_2) |-> {add_dirram,reset_dirram,add_col,reset_col,add_ascci,reset_ascci,leer_rom,leer_ram,init,run_efect} == 10'b0_0_0_0_0_0_1_0_0_0);
  assert property ((current_state==state_3) |-> {add_dirram,reset_dirram,add_col,reset_col,add_ascci,reset_ascci,leer_rom,leer_ram,init,run_efect} == 10'b0_0_0_0_0_0_1_0_0_0);
  assert property ((current_state==state_4) |-> {add_dirram,reset_dirram,add_col,reset_col,add_ascci,reset_ascci,leer_rom,leer_ram,init,run_efect} == 10'b1_0_1_0_0_0_1_0_0_0);
  assert property ((current_state==state_5) |-> {add_dirram,reset_dirram,add_col,reset_col,add_ascci,reset_ascci,leer_rom,leer_ram,init,run_efect} == 10'b1_0_0_1_1_0_0_0_0_0);
  assert property ((current_state==check)   |-> {add_dirram,reset_dirram,add_col,reset_col,add_ascci,reset_ascci,leer_rom,leer_ram,init,run_efect} == 10'b0_0_0_0_0_0_0_1_0_1);

  // Mutually exclusive control pairs
  assert property (!(add_dirram && reset_dirram));
  assert property (!(add_col    && reset_col));
  assert property (!(add_ascci  && reset_ascci));
  assert property (!(leer_rom   && leer_ram));

  // Transition function (one-cycle next-state)
  assert property ((current_state==start   &&  new_string) |=> current_state==state_1p);
  assert property ((current_state==start   && !new_string) |=> current_state==start);

  assert property ( (current_state==state_1p)               |=> current_state==state_1);
  assert property ( (current_state==state_1)                |=> current_state==state_2);

  assert property ((current_state==state_2 &&  done)        |=> current_state==state_3);
  assert property ((current_state==state_2 && !done)        |=> current_state==state_2);

  assert property ( (current_state==state_3)                |=> current_state==state_4);

  assert property ((current_state==state_4 &&  top_col)     |=> current_state==state_5);
  assert property ((current_state==state_4 && !top_col)     |=> current_state==state_3);

  assert property ((current_state==state_5 &&  top_ascci)   |=> current_state==check);
  assert property ((current_state==state_5 && !top_ascci)   |=> current_state==state_1);

  assert property ((current_state==check   &&  new_string)  |=> current_state==start);
  assert property ((current_state==check   && !new_string)  |=> current_state==check);

  // Basic reachability coverage
  cover property (current_state==start);
  cover property (current_state==state_1p);
  cover property (current_state==state_1);
  cover property (current_state==state_2);
  cover property (current_state==state_3);
  cover property (current_state==state_4);
  cover property (current_state==state_5);
  cover property (current_state==check);

  // Transition coverage (both branches where applicable)
  cover property ((current_state==start   &&  new_string) ##1 (current_state==state_1p));
  cover property ((current_state==start   && !new_string) ##1 (current_state==start));
  cover property ( (current_state==state_1p)               ##1 (current_state==state_1));
  cover property ( (current_state==state_1)                ##1 (current_state==state_2));
  cover property ((current_state==state_2 &&  done)        ##1 (current_state==state_3));
  cover property ((current_state==state_2 && !done)        ##1 (current_state==state_2));
  cover property ( (current_state==state_3)                ##1 (current_state==state_4));
  cover property ((current_state==state_4 &&  top_col)     ##1 (current_state==state_5));
  cover property ((current_state==state_4 && !top_col)     ##1 (current_state==state_3));
  cover property ((current_state==state_5 &&  top_ascci)   ##1 (current_state==check));
  cover property ((current_state==state_5 && !top_ascci)   ##1 (current_state==state_1));
  cover property ((current_state==check   &&  new_string)  ##1 (current_state==start));
  cover property ((current_state==check   && !new_string)  ##1 (current_state==check));

  // End-to-end “happy” path coverage
  cover property ( (current_state==start && new_string)
                   ##1 (current_state==state_1p)
                   ##1 (current_state==state_1)
                   ##1 (current_state==state_2 && done)
                   ##1 (current_state==state_3)
                   ##1 (current_state==state_4 && top_col)
                   ##1 (current_state==state_5 && top_ascii) ); // optional: continue to check and back to start
  // Correct typo in signal name for the previous cover if needed:
  // Alternate full cycle:
  cover property ( (current_state==start && new_string)
                   ##1 (current_state==state_1p)
                   ##1 (current_state==state_1)
                   ##1 (current_state==state_2 && done)
                   ##1 (current_state==state_3)
                   ##1 (current_state==state_4 && top_col)
                   ##1 (current_state==state_5 && top_ascci)
                   ##1 (current_state==check && new_string)
                   ##1 (current_state==start) );
endmodule