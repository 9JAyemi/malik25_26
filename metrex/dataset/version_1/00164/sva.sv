// SVA for note_mono: concise, high-value checks and coverage
// Bind these assertions to the DUT (no DUT/testbench changes needed)

module note_mono_sva (note_mono dut);

  // Default SVA clocking and reset
  default clocking cb @(posedge dut.clk); endclocking
  default disable iff (dut.rst);

  // Helper: compute current max note across active list entries [0..top_ptr-1]
  function automatic [6:0] max_list;
    input [6:0] arr [0:dut.MNOTES];
    input [dut.BIT_WIDTH:0] tp;
    integer i;
    reg [6:0] m;
    begin
      m = 7'd0;
      for (i = 0; i < tp; i++) begin
        if (arr[i] > m) m = arr[i];
      end
      max_list = m;
    end
  endfunction

  // Basic invariants
  // State encodings valid
  assert property (dut.state inside {dut.INITIAL, dut.NOTE_ON, dut.NOTE_OFF, dut.READY});
  assert property (dut.note_on_state inside {dut.ST_SEARCH, dut.IN_SEARCH, dut.END_SEARCH, dut.GETMAX});
  assert property (dut.note_off_state inside {dut.ST_SEARCH, dut.IN_SEARCH, dut.END_SEARCH});

  // Pointers and indices in range
  assert property (dut.top_ptr <= dut.MAX_NOTES);
  assert property ((dut.state==dut.NOTE_ON && dut.note_on_state==dut.IN_SEARCH) |-> (dut.addr <= dut.top_ptr));
  assert property ((dut.state==dut.NOTE_OFF && dut.note_off_state==dut.IN_SEARCH) |-> (dut.addr <= dut.top_ptr));
  // Prevent overflow write on insert at end
  assert property ((dut.state==dut.NOTE_ON && dut.note_on_state==dut.END_SEARCH && !dut.searched) |-> $past(dut.top_ptr) < dut.MAX_NOTES);

  // t_note sampling on any event
  assert property ((dut.note_on || dut.note_off) |=> (dut.t_note == $past(dut.note)));

  // out_note gating and READY semantics
  assert property ((!dut.out_gate) |-> (dut.out_note == 7'd0));
  assert property ((dut.out_gate) |-> (dut.out_note == dut.t_out_note));
  assert property ((dut.state==dut.READY) |-> (dut.out_gate == (dut.top_ptr > 0)));

  // Output note equals max(list) whenever READY and non-empty
  assert property ((dut.state==dut.READY && dut.top_ptr>0) |-> (dut.t_out_note == max_list(dut.list, dut.top_ptr)));

  // Transaction entry clears searched
  assert property (($past(dut.state)==dut.READY && dut.state==dut.NOTE_ON) |-> (dut.searched==1'b0));
  assert property (($past(dut.state)==dut.READY && dut.state==dut.NOTE_OFF) |-> (dut.searched==1'b0));

  // NOTE_ON: empty list fast path inserts and updates outputs correctly
  property p_note_on_first_insert;
    ($rose(dut.note_on) && $past(dut.state)==dut.READY && $past(dut.top_ptr)==0)
    |=> (dut.state==dut.NOTE_ON && dut.note_on_state==dut.ST_SEARCH)
    ##1 (dut.state==dut.READY && dut.top_ptr==1 && dut.out_gate && dut.t_out_note==dut.t_note && dut.list[0]==dut.t_note);
  endproperty
  assert property (p_note_on_first_insert);

  // NOTE_ON: end of search outcomes
  // If duplicate found, no size change
  assert property ((dut.state==dut.NOTE_ON && dut.note_on_state==dut.END_SEARCH && dut.searched) |=> (dut.state==dut.READY && dut.top_ptr==$past(dut.top_ptr)));
  // If new note, size increments by one and gate is on
  assert property ((dut.state==dut.NOTE_ON && dut.note_on_state==dut.END_SEARCH && !dut.searched) |=> (dut.top_ptr==$past(dut.top_ptr)+1 && dut.out_gate));

  // NOTE_OFF: size change only if found; out_gate updated accordingly next READY
  assert property ((dut.state==dut.NOTE_OFF && dut.note_off_state==dut.IN_SEARCH && dut.addr==dut.top_ptr)
                   |=> (dut.top_ptr == ($past(dut.top_ptr) - ($past(dut.searched) ? 1 : 0))));
  assert property ((dut.state==dut.NOTE_OFF && dut.note_off_state==dut.END_SEARCH) |=> (dut.state==dut.READY && dut.out_gate==(dut.top_ptr>0)));

  // Reset/initialization behavior
  assert property ($rose(dut.rst) |=> dut.state==dut.INITIAL);
  // After leaving reset, reach READY next cycle
  assert property ($fell(dut.rst) |=> dut.state==dut.READY);

  // Top_ptr changes only within NOTE_ON/NOTE_OFF
  assert property ($changed(dut.top_ptr) |-> (dut.state inside {dut.NOTE_ON, dut.NOTE_OFF}));

  // Coverage: key scenarios

  // Cover: insert first note (empty -> one)
  cover property ($rose(dut.note_on) && $past(dut.state)==dut.READY && $past(dut.top_ptr)==0
                  ##2 (dut.state==dut.READY && dut.top_ptr==1 && dut.out_gate));

  // Cover: insert new higher note when non-empty updates t_out_note
  cover property (dut.state==dut.NOTE_ON && dut.note_on_state==dut.END_SEARCH && !dut.searched
                  && (dut.t_note > $past(max_list(dut.list, dut.top_ptr)))
                  ##1 (dut.state==dut.READY && dut.t_out_note==max_list(dut.list, dut.top_ptr)));

  // Cover: duplicate note_on does not change size
  cover property (dut.state==dut.NOTE_ON && dut.note_on_state==dut.END_SEARCH && dut.searched ##1 (dut.state==dut.READY && $stable(dut.top_ptr)));

  // Cover: fill to capacity
  cover property (dut.state==dut.READY && dut.top_ptr==dut.MAX_NOTES);

  // Cover: attempt insert when full does not overflow
  cover property (dut.state==dut.NOTE_ON && dut.note_on_state==dut.END_SEARCH && !dut.searched && $past(dut.top_ptr)==dut.MAX_NOTES);

  // Cover: drain to empty and gate deasserts
  cover property (dut.state==dut.NOTE_OFF && dut.note_off_state==dut.END_SEARCH ##1 (dut.state==dut.READY && dut.top_ptr==0 && !dut.out_gate));

endmodule

// Bind into all instances of note_mono
bind note_mono note_mono_sva sva_inst(.dut(this));