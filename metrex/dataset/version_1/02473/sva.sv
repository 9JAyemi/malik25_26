// SVA for lifo_memory
// Bind into the DUT to observe internals (pointer, memory)
module lifo_memory_sva #(parameter int DEPTH = 8) ();

  // Directly reference bound instance signals
  // clk, rst, wr_en, data_in, data_out, pointer, memory[]

  default clocking cb @(posedge clk); endclocking

  // Event encodings as implemented (case on {wr_en,pointer} vs 2-bit items)
  // These reflect the DUT's coded behavior, not an intended spec.
  wire write_ev = (!wr_en) && (pointer == 3'd1); // matches 4'b0001
  wire read_ev  = (!wr_en) && (pointer == 3'd2); // matches 4'b0010

  // Basic sanity: no X on key signals when not in reset
  assert property (disable iff (rst) !$isunknown({wr_en, pointer, data_out}));

  // Reset: synchronous, clears pointer and data_out
  assert property (rst |=> (pointer == 3'd0) && (data_out == 8'h00));

  // Default path (neither write nor read): pointer and data_out hold value
  assert property (disable iff (rst)
                   !(write_ev || read_ev) |=> (pointer == $past(pointer)) && (data_out == $past(data_out)));

  // Write: pointer increments, memory at old pointer gets data_in
  assert property (disable iff (rst)
                   write_ev |=> (pointer == $past(pointer)+1));
  assert property (disable iff (rst)
                   write_ev |=> memory[$past(pointer)] == $past(data_in));

  // Read: pointer decrements, data_out returns last item
  assert property (disable iff (rst)
                   read_ev |=> (pointer == $past(pointer)-1));
  assert property (disable iff (rst)
                   read_ev |=> data_out == $past(memory[$past(pointer)-1]));

  // No wrap/overflow/underflow (detects missing bounds checks)
  assert property (disable iff (rst) write_ev |=> pointer > $past(pointer));
  assert property (disable iff (rst) read_ev  |=> pointer < $past(pointer));

  // Memory stability:
  // - No write: entire memory holds
  genvar i;
  generate
    for (i=0; i<DEPTH; i++) begin : g_mem_hold_no_write
      assert property (disable iff (rst) !write_ev |=> memory[i] == $past(memory[i]));
    end
  endgenerate
  // - During write: only the targeted entry may change; others hold
  generate
    for (i=0; i<DEPTH; i++) begin : g_mem_hold_on_write_other
      assert property (disable iff (rst)
                       write_ev && ($past(pointer) != i) |=> memory[i] == $past(memory[i]));
    end
  endgenerate
  // - During read: memory is never modified
  generate
    for (i=0; i<DEPTH; i++) begin : g_mem_hold_on_read
      assert property (disable iff (rst) read_ev |=> memory[i] == $past(memory[i]));
    end
  endgenerate

  // Functional LIFO spot-check (write then read returns the written data)
  cover property (write_ev ##1 read_ev ##1 (data_out == $past(data_in,2)));

  // Coverage: hit both coded cases and boundaries
  cover property (write_ev);
  cover property (read_ev);
  cover property (pointer == 0);
  cover property (pointer == (DEPTH-1));

endmodule

// Bind into all lifo_memory instances
bind lifo_memory lifo_memory_sva #(.DEPTH(depth)) lifo_memory_sva_b();