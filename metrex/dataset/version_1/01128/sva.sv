// SVA for mux_ff — bindable checker
module mux_ff_sva (
  input  logic        clk,
  input  logic [3:0]  in,
  input  logic [1:0]  sel,
  input  logic        q,
  input  logic        selected_signal
);

  default clocking cb @(posedge clk); endclocking

  // Track first clock to guard $past usage
  logic init_done;
  initial init_done = 1'b0;
  always @(posedge clk) init_done <= 1'b1;

  // 1) Combinational mux correctness: selected_signal matches in[sel] when inputs known
  assert property ( !$isunknown({sel,in}) |-> (selected_signal === in[sel]) )
    else $error("selected_signal != in[sel]");

  // 2) Registered behavior: q equals previous cycle's selected input bit
  assert property ( disable iff (!init_done)
                    (!$isunknown($past({sel,in}))) |-> (q == $past(in)[$past(sel)]) )
    else $error("q does not equal prior cycle in[sel]");

  // 3) No X on outputs after first clock
  assert property ( disable iff (!init_done) !$isunknown(q) )
    else $error("q is X/Z after initialization");

  // 4) q changes only on clock rising edge (no glitches)
  assert property (@(posedge clk or q) $changed(q) |-> $rose(clk))
    else $error("q changed outside posedge clk");

  // 5) Coverage: exercise all select values
  cover property ( disable iff (!init_done) sel == 2'b00 );
  cover property ( disable iff (!init_done) sel == 2'b01 );
  cover property ( disable iff (!init_done) sel == 2'b10 );
  cover property ( disable iff (!init_done) sel == 2'b11 );

  // 6) Coverage: capture of each selected bit into q
  cover property ( disable iff (!init_done) sel==2'b00 ##1 q == $past(in[0]) );
  cover property ( disable iff (!init_done) sel==2'b01 ##1 q == $past(in[1]) );
  cover property ( disable iff (!init_done) sel==2'b10 ##1 q == $past(in[2]) );
  cover property ( disable iff (!init_done) sel==2'b11 ##1 q == $past(in[3]) );

  // 7) Coverage: q toggles
  cover property ( disable iff (!init_done) q != $past(q) );

endmodule

// Bind into DUT (place alongside DUT or in a testbench package/file)
bind mux_ff mux_ff_sva u_mux_ff_sva (
  .clk             (clk),
  .in              (in),
  .sel             (sel),
  .q               (q),
  .selected_signal (selected_signal)
);