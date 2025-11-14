// SVA for fifo. Bind this to the DUT.
// Usage: bind fifo fifo_sva i_fifo_sva();

module fifo_sva;

  // Helper functions
  function automatic [3:0] inc4 (input [3:0] v);
    inc4 = (v==4'd15) ? 4'd0 : (v + 4'd1);
  endfunction

  function automatic [3:0] diff16(input [3:0] w, input [3:0] r);
    diff16 = (w>=r) ? (w - r) : (w + 4'd16 - r);
  endfunction

  // Default SVA context
  default clocking cb @(posedge clock); endclocking
  default disable iff (reset);

  // Optional environment assumptions (comment out if you want to catch violations)
  assume property ( (!fifo_full) or (!write) );  // no write when full
  assume property ( (!fifo_empty) or (!read) );  // no read when empty

  // Reset behavior
  assert property ( reset |-> (read_ptr==0 && write_ptr==0 && counter==0 &&
                               fifo_out==16'h0 && fifo_empty && !fifo_full) );

  // Flags reflect counter
  assert property ( fifo_empty == (counter==0) );
  assert property ( fifo_full  == (counter==4'd15) );

  // X/Z checks after reset deassertion
  assert property ( !$isunknown({fifo_empty,fifo_full,fifo_out,read_ptr,write_ptr,counter}) );

  // Counter updates
  assert property ( (!read && !write) |=> counter == $past(counter) );
  assert property ( ( write && !read && !fifo_full) |=> counter == $past(counter)+1 );
  assert property ( (!write &&  read && !fifo_empty) |=> counter == $past(counter)-1 );
  assert property ( ( read && write && counter>0)    |=> counter == $past(counter) );
  assert property ( ( read && write && counter==0)   |=> counter == 0 );

  // Pointer updates (this will flag the DUT bug in 2'b11 branch)
  assert property ( ( write && !read && !fifo_full) |=> write_ptr == inc4($past(write_ptr)) && read_ptr == $past(read_ptr) );
  assert property ( (!write &&  read && !fifo_empty)|=> read_ptr  == inc4($past(read_ptr))  && write_ptr== $past(write_ptr) );
  assert property ( ( read && write && counter>0)   |=> write_ptr == inc4($past(write_ptr)) && read_ptr == inc4($past(read_ptr)) );
  assert property ( ( read && write && counter==0)  |=> write_ptr == $past(write_ptr)       && read_ptr == $past(read_ptr) );

  // Pointer/counter consistency (only require when no illegal ops)
  assert property ( ((!write || !fifo_full) && (!read || !fifo_empty)) |-> counter == diff16(write_ptr, read_ptr) );

  // Memory write correctness
  assert property ( ( write && !read && !fifo_full) |=> ram[$past(write_ptr)] == $past(fifo_in) );
  assert property ( ( read && write && counter>0 )  |=> ram[$past(write_ptr)] == $past(fifo_in) );

  // Data out correctness
  assert property ( (!write && read && !fifo_empty) |-> fifo_out == $past(ram[$past(read_ptr)]) );
  assert property ( ( read && write && counter>0 )  |-> fifo_out == $past(ram[$past(read_ptr)]) );
  assert property ( ( read && write && counter==0 ) |-> fifo_out == fifo_in );

  // FIFO ordering: a write (without simultaneous read) eventually appears on the matching read of that slot
  property fifo_ordering;
    logic [15:0] d; logic [3:0] idx;
    (write && !read && !fifo_full, d = fifo_in, idx = write_ptr)
      |->
    ##[1:$] (read && !fifo_empty && (read_ptr == idx)) |-> (fifo_out == d);
  endproperty
  assert property (fifo_ordering);

  // Coverage: key scenarios
  cover property ( !read && !write );                                      // idle
  cover property ( write && !read && !fifo_full );                         // write
  cover property ( !write && read && !fifo_empty );                        // read
  cover property ( read && write && counter==0 );                          // pass-through on empty
  cover property ( read && write && counter>0 );                           // simultaneous R/W with occupancy
  cover property ( (write_ptr==4'd15) && write && !read && !fifo_full ##1 write_ptr==4'd0 ); // write wrap
  cover property ( (read_ptr==4'd15)  && read  && !write && !fifo_empty ##1 read_ptr==4'd0 );// read wrap
  cover property ( counter==0 ##[1:$] write && !read && !fifo_full ##[1:$] counter==4'd15 ); // reach full
  cover property ( counter==4'd15 ##[1:$] read && !write && !fifo_empty ##[1:$] counter==0 ); // drain to empty

endmodule

bind fifo fifo_sva i_fifo_sva();