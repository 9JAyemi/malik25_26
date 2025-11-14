// SVA for UnorderedSet: bind-in module focused on correctness and concise full coverage
// Drop this after the DUT and let tools bind it, or inline inside the DUT for direct visibility.

module UnorderedSet_sva #(
  parameter int DEPTH      = 16,
  parameter int ITER_SIZE  = 4,
  parameter int KEY_SIZE   = 16
) ();

  default clocking cb @(posedge clk); endclocking

  // Helpers on current state
  function automatic bit any_valid_cur();
    bit v = 0;
    for (int k=0;k<DEPTH;k++) v |= slot_valid[k];
    return v;
  endfunction

  function automatic int first_valid_cur();
    for (int k=0;k<DEPTH;k++) if (slot_valid[k]) return k;
    return -1;
  endfunction

  function automatic int first_after_cur(input int idx);
    for (int k=0;k<DEPTH;k++) if (slot_valid[k] && (k>idx)) return k;
    return -1;
  endfunction

  function automatic bit dup_present_cur();
    bit f = 0;
    for (int k=0;k<DEPTH;k++) if (slot_valid[k] && slot_key[k]==insert_key) f = 1;
    return f;
  endfunction

  function automatic bit exists_free_cur();
    for (int k=0;k<DEPTH;k++) if (!slot_valid[k]) return 1;
    return 0;
  endfunction

  function automatic int first_free_cur();
    for (int k=0;k<DEPTH;k++) if (!slot_valid[k]) return k;
    return -1;
  endfunction

  function automatic bit any_rise_cur();
    bit r = 0;
    for (int k=0;k<DEPTH;k++) r |= (!$past(slot_valid[k]) && slot_valid[k]);
    return r;
  endfunction

  // Invariants: no duplicate keys among valid slots
  genvar i,j;
  generate
    for (i=0;i<DEPTH;i++) begin : G_I
      for (j=i+1;j<DEPTH;j++) begin : G_J
        assert property ( !(slot_valid[i] && slot_valid[j] && slot_key[i]==slot_key[j]) )
          else $error("Duplicate key present at two valid slots %0d and %0d", i, j);
      end
    end
  endgenerate

  // insert_ok only asserted when insert_en
  assert property ( insert_ok |-> insert_en )
    else $error("insert_ok asserted without insert_en");

  // Duplicate insert: must report ok, and must not create any new valid bit
  assert property ( insert_en && dup_present_cur() |-> insert_ok )
    else $error("Duplicate insert did not assert insert_ok");
  assert property ( insert_en && dup_present_cur() |=> !any_rise_cur() )
    else $error("Duplicate insert caused a slot_valid rise");

  // Successful insert (has free, no dup): report ok now, and next cycle the first-free slot becomes valid with correct key
  assert property ( insert_en && !dup_present_cur() && exists_free_cur() |-> insert_ok )
    else $error("Insert with free slot did not assert insert_ok");
  assert property ( insert_en && !dup_present_cur() && exists_free_cur()
                    |=> slot_valid[$past(first_free_cur())]
                        && slot_key[$past(first_free_cur())] == $past(insert_key) )
    else $error("Insert did not occupy first free slot or wrong key stored");

  // Insert when full and no dup: must not report ok, and must not create any new valid bit
  assert property ( insert_en && !dup_present_cur() && !exists_free_cur() |-> !insert_ok )
    else $error("Insert on full set asserted insert_ok");
  assert property ( insert_en && !dup_present_cur() && !exists_free_cur() |=> !any_rise_cur() )
    else $error("Insert on full set created a new valid slot");

  // Remove: target slot must be cleared next cycle
  assert property ( remove_en |=> !slot_valid[$past(remove_iter)] )
    else $error("Remove did not clear the specified slot");

  // Iterator semantics (iter_begin has priority over iter_inc)
  // iter_begin
  assert property (
    iter_begin |-> ( any_valid_cur()
                     ? (!iter_end && iter_next == first_valid_cur()
                        && slot_valid[iter_next]
                        && iter_key == slot_key[iter_next])
                     : (iter_end && iter_next == 0) )
  ) else $error("iter_begin semantics violated");

  // iter_inc (only when iter_begin is not asserted)
  assert property (
    !iter_begin && iter_inc |-> ( (first_after_cur(iter_in) != -1)
                     ? (!iter_end && iter_next == first_after_cur(iter_in)
                        && slot_valid[iter_next]
                        && iter_key == slot_key[iter_next])
                     : (iter_end && iter_next == 0) )
  ) else $error("iter_inc semantics violated");

  // When idle: outputs at default
  assert property ( !iter_begin && !iter_inc |-> (iter_end && iter_next == 0) )
    else $error("Iterator defaults violated when idle");

  // Iterator sanity: when not at end, iter_next is in range and key matches slot
  assert property ( !iter_end |-> (iter_next < DEPTH) )
    else $error("iter_next out of range when iter_end==0");
  assert property ( !iter_end |-> (slot_valid[iter_next] && iter_key == slot_key[iter_next]) )
    else $error("Iterator key/valid mismatch");

  // Coverage
  cover property ( insert_en && !dup_present_cur() && exists_free_cur()
                   ##1 slot_valid[$past(first_free_cur())] );
  cover property ( insert_en && dup_present_cur() );
  cover property ( insert_en && !dup_present_cur() && !exists_free_cur() );

  cover property ( remove_en && slot_valid[remove_iter] );
  cover property ( remove_en && !slot_valid[remove_iter] );
  cover property ( insert_en && remove_en );

  cover property ( iter_begin && any_valid_cur() );
  cover property ( iter_begin && !any_valid_cur() );
  cover property ( !iter_begin && iter_inc && (first_after_cur(iter_in) != -1) );
  cover property ( !iter_begin && iter_inc && (first_after_cur(iter_in) == -1) );

endmodule

bind UnorderedSet UnorderedSet_sva #(.DEPTH(DEPTH), .ITER_SIZE(ITER_SIZE), .KEY_SIZE(KEY_SIZE)) UnorderedSet_sva_i();