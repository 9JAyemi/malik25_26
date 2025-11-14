// SystemVerilog Assertions for note2dds_3st_gen
// Bind this file to the DUT. Focused, concise checks + coverage.

bind note2dds_3st_gen note2dds_3st_gen_sva sva();

module note2dds_3st_gen_sva;
  // Inserted into note2dds_3st_gen scope by bind; can reference internals directly.

  default clocking cb @(posedge CLK); endclocking

  // Make $past() safe and ignore first cycle/unknowns
  logic past_valid;
  initial past_valid = 1'b0;
  always @(posedge CLK) past_valid <= 1'b1;

  default disable iff (!past_valid || $isunknown({NOTE}));

  // Basic sanity
  assert property (!$isunknown({addr, divider, ADDER}));
  assert property (note_a < 7'd12);
  assert property (addr inside {[4'd0:4'd11]});
  assert property (divider inside {[4'd0:4'd10]});
  assert property (ADDER != 32'd0);

  // Combinational mapping correctness
  assert property (note_a[3:0] == (NOTE % 7'd12)[3:0]);
  assert property ((NOTE < 7'd120) |-> (div_val == (4'd10 - (NOTE/7'd12))));
  assert property ((NOTE >= 7'd120) |-> (div_val == 4'd0));
  assert property ((NOTE >= 7'd120) |-> (note_a == (NOTE - 7'd120)));

  // Registered pipeline behavior (1-cycle latency from NOTE)
  assert property (addr    == $past(note_a[3:0]));
  assert property (divider == $past(div_val));

  // Output correctness
  assert property (ADDER == (ADDER_tbl[addr] >> divider));
  assert property (ADDER == (ADDER_tbl[$past(note_a[3:0])] >> $past(div_val)));

  // Optional: ADDER_tbl upper entries are zero (as coded)
  assert property (ADDER_tbl[4'd12] == 32'd0);
  assert property (ADDER_tbl[4'd13] == 32'd0);
  assert property (ADDER_tbl[4'd14] == 32'd0);
  assert property (ADDER_tbl[4'd15] == 32'd0);

  // Boundary behavior (covers)
  // Hit each octave boundary and top saturation range
  cover property (NOTE == 7'd0  && note_a==0 && div_val==10);
  cover property (NOTE == 7'd12 && note_a==0 && div_val==9);
  cover property (NOTE == 7'd24 && note_a==0 && div_val==8);
  cover property (NOTE == 7'd36 && note_a==0 && div_val==7);
  cover property (NOTE == 7'd48 && note_a==0 && div_val==6);
  cover property (NOTE == 7'd60 && note_a==0 && div_val==5);
  cover property (NOTE == 7'd72 && note_a==0 && div_val==4);
  cover property (NOTE == 7'd84 && note_a==0 && div_val==3);
  cover property (NOTE == 7'd96 && note_a==0 && div_val==2);
  cover property (NOTE == 7'd108 && note_a==0 && div_val==1);
  cover property (NOTE inside {[7'd120:7'd127]} && div_val==0);

  // Compact functional coverage for full value space
  covergroup cg @(posedge CLK);
    coverpoint note_a[3:0] { bins all_notes[] = {[0:11]}; }
    coverpoint div_val     { bins all_divs[]  = {[0:10]}; }
    // Optional cross to see exercised combinations (may be partially unreachable)
    // cross note_a, div_val;
  endgroup
  cg cg_i = new();

endmodule