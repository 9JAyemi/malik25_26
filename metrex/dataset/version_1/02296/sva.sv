// SVA checker bound into simple_cpu
module simple_cpu_sva;
  default clocking cb @(posedge clk); endclocking

  // Helpers (all sampled from prior cycle)
  let p_pc    = $past(program_counter);
  let p_addr  = $past(address);
  let p_acc   = $past(accumulator);
  let p_instr = $past(memory[p_pc]);
  let p_mem_a = $past(memory[p_addr]);

  // Data-out mirrors accumulator
  assert property (data_out == accumulator);

  // Reset behavior (synchronous)
  assert property (@(posedge clk) reset |=> accumulator==16'h0 && program_counter==8'h0);
  assert property (@(posedge clk) reset && $past(reset) |-> accumulator==16'h0 && program_counter==8'h0);

  // Program counter increments every active cycle
  assert property (disable iff (reset) program_counter == p_pc + 8'h1);

  // Accumulator semantics per opcode (instruction matches full 16'h0..6 as coded)
  assert property (disable iff (reset) (p_instr == 16'h0) |-> accumulator == p_acc + p_mem_a);
  assert property (disable iff (reset) (p_instr == 16'h1) |-> accumulator == p_acc - p_mem_a);
  assert property (disable iff (reset) (p_instr == 16'h2) |-> accumulator == (p_acc & p_mem_a));
  assert property (disable iff (reset) (p_instr == 16'h3) |-> accumulator == (p_acc | p_mem_a));
  assert property (disable iff (reset) (p_instr == 16'h4) |-> accumulator == (p_acc ^ p_mem_a));
  assert property (disable iff (reset) (p_instr == 16'h5) |-> accumulator == p_mem_a);
  assert property (disable iff (reset) (p_instr == 16'h6) |-> accumulator == p_acc);
  assert property (disable iff (reset) !(p_instr inside {16'h0,16'h1,16'h2,16'h3,16'h4,16'h5,16'h6}) |-> accumulator == p_acc);

  // Memory write happens only for opcode 6 and writes prior accumulator
  assert property (disable iff (reset) (p_instr == 16'h6) |-> memory[p_addr] == p_acc);
  assert property (disable iff (reset) (p_instr != 16'h6) |-> memory[p_addr] == p_mem_a);

  // No unknowns on key signals when active
  assert property (disable iff (reset) !$isunknown({address, accumulator, program_counter, data_out}));

  // Coverage: each opcode, default path, store, and PC wrap
  cover property (disable iff (reset) p_instr == 16'h0);
  cover property (disable iff (reset) p_instr == 16'h1);
  cover property (disable iff (reset) p_instr == 16'h2);
  cover property (disable iff (reset) p_instr == 16'h3);
  cover property (disable iff (reset) p_instr == 16'h4);
  cover property (disable iff (reset) p_instr == 16'h5);
  cover property (disable iff (reset) p_instr == 16'h6);
  cover property (disable iff (reset) !(p_instr inside {16'h0,16'h1,16'h2,16'h3,16'h4,16'h5,16'h6}));
  cover property (disable iff (reset) p_pc==8'hFF && program_counter==8'h00);
  cover property (disable iff (reset) (p_instr==16'h6) && memory[p_addr]==p_acc);
endmodule

bind simple_cpu simple_cpu_sva sva();