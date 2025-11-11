// Bindable SVA checker for mux4to1
module mux4to1_sva (
  input  logic [3:0] data_in,
  input  logic [1:0] sel,
  input  logic       data_out
);

  // sel must be 2-state (avoids latchy behavior on X/Z case decode)
  assert property (@(sel) !$isunknown(sel))
    else $error("mux4to1: sel has X/Z");

  // Functional correctness (selected bit appears at output)
  assert property (@(sel or data_in) (sel==2'b00) |-> ##0 (data_out === data_in[0]))
    else $error("mux4to1: sel=00 mismatch");
  assert property (@(sel or data_in) (sel==2'b01) |-> ##0 (data_out === data_in[1]))
    else $error("mux4to1: sel=01 mismatch");
  assert property (@(sel or data_in) (sel==2'b10) |-> ##0 (data_out === data_in[2]))
    else $error("mux4to1: sel=10 mismatch");
  assert property (@(sel or data_in) (sel==2'b11) |-> ##0 (data_out === data_in[3]))
    else $error("mux4to1: sel=11 mismatch");

  // Output must be known when selected input is known
  assert property (@(sel or data_in) (sel==2'b00 && !$isunknown(data_in[0])) |-> ##0 !$isunknown(data_out))
    else $error("mux4to1: sel=00 output X/Z with known input");
  assert property (@(sel or data_in) (sel==2'b01 && !$isunknown(data_in[1])) |-> ##0 !$isunknown(data_out))
    else $error("mux4to1: sel=01 output X/Z with known input");
  assert property (@(sel or data_in) (sel==2'b10 && !$isunknown(data_in[2])) |-> ##0 !$isunknown(data_out))
    else $error("mux4to1: sel=10 output X/Z with known input");
  assert property (@(sel or data_in) (sel==2'b11 && !$isunknown(data_in[3])) |-> ##0 !$isunknown(data_out))
    else $error("mux4to1: sel=11 output X/Z with known input");

  // Output changes only if sel or the selected input changes
  assert property (@(sel or data_in or data_out)
                   (sel==2'b00 && $stable(sel) && $changed(data_out)) |-> $changed(data_in[0]))
    else $error("mux4to1: data_out changed without data_in[0]/sel change");
  assert property (@(sel or data_in or data_out)
                   (sel==2'b01 && $stable(sel) && $changed(data_out)) |-> $changed(data_in[1]))
    else $error("mux4to1: data_out changed without data_in[1]/sel change");
  assert property (@(sel or data_in or data_out)
                   (sel==2'b10 && $stable(sel) && $changed(data_out)) |-> $changed(data_in[2]))
    else $error("mux4to1: data_out changed without data_in[2]/sel change");
  assert property (@(sel or data_in or data_out)
                   (sel==2'b11 && $stable(sel) && $changed(data_out)) |-> $changed(data_in[3]))
    else $error("mux4to1: data_out changed without data_in[3]/sel change");

  // Coverage: hit each select and observe propagation on changes
  cover property (@(sel) sel==2'b00);
  cover property (@(sel) sel==2'b01);
  cover property (@(sel) sel==2'b10);
  cover property (@(sel) sel==2'b11);

  cover property (@(sel or data_in) (sel==2'b00 && $changed(data_in[0]) && $stable(sel)) ##0 (data_out === data_in[0]));
  cover property (@(sel or data_in) (sel==2'b01 && $changed(data_in[1]) && $stable(sel)) ##0 (data_out === data_in[1]));
  cover property (@(sel or data_in) (sel==2'b10 && $changed(data_in[2]) && $stable(sel)) ##0 (data_out === data_in[2]));
  cover property (@(sel or data_in) (sel==2'b11 && $changed(data_in[3]) && $stable(sel)) ##0 (data_out === data_in[3]));

endmodule

// Bind the checker to the DUT
bind mux4to1 mux4to1_sva mux4to1_sva_i (.*);