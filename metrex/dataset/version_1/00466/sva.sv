// SVA for note2dds. Bind this file to the DUT.
// Concise, functionally-focused checks with useful coverage.

module note2dds_sva
(
  input  logic        clk,
  input  logic [8:0]  note,
  input  logic [31:0] adder,
  input  logic [3:0]  addr,
  input  logic [3:0]  divider,
  input  logic [31:0] adder_tbl [0:15],
  input  logic [5:0]  diap,
  input  logic [6:0]  c_addr
);

  bit started;
  always_ff @(posedge clk) started <= 1'b1;

  // Combinational math is correct (sampled on clk)
  assert property (@(posedge clk) disable iff (!started)
    diap == (note / 9'd12)
  );

  assert property (@(posedge clk) disable iff (!started)
    c_addr == (note % 9'd12)
  );

  assert property (@(posedge clk) disable iff (!started)
    c_addr < 7'd12
  );

  // Pipeline/registering behavior
  assert property (@(posedge clk) disable iff (!started)
    addr == $past(c_addr[3:0])
  );

  // Never index uninitialized table entries (12..15)
  assert property (@(posedge clk) disable iff (!started)
    addr <= 4'd11
  );

  // Divider is modulo-16 of intended value (captures width truncation)
  assert property (@(posedge clk) disable iff (!started)
    divider == $past( (6'd42 - diap) & 4'hF )
  );

  // End-to-end: output equals table(addr) >> divider, mapped from prior-cycle note
  assert property (@(posedge clk) disable iff (!started)
    adder == (adder_tbl[$past(c_addr[3:0])] >> $past( (6'd42 - diap) & 4'hF ))
  );

  // Table contents never change after start
  genvar i;
  generate
    for (i=0; i<16; i++) begin : G_TBL_STABLE
      assert property (@(posedge clk) disable iff (!started)
        $stable(adder_tbl[i])
      );
    end
  endgenerate

  // Sanity on zero-initialized upper table slots
  generate
    for (i=12; i<16; i++) begin : G_TBL_ZERO
      assert property (@(posedge clk) disable iff (!started)
        adder_tbl[i] == 32'd0
      );
    end
  endgenerate

  // Monotonic/carry behavior across semitone and octave boundaries
  assert property (@(posedge clk) disable iff (!started)
    (note == $past(note)+1) && ((note/9'd12) == ($past(note)/9'd12))
    |-> c_addr == $past(c_addr) + 1
  );

  assert property (@(posedge clk) disable iff (!started)
    (note == $past(note)+1) && ((note % 9'd12) == 0)
    |-> (c_addr == 0) && (diap == $past(diap)+1)
  );

  // Coverage: extremes, boundaries, and notable conditions
  cover property (@(posedge clk) started && (diap == 6'd0)  && (note == 9'd0)   && (c_addr == 7'd0));
  cover property (@(posedge clk) started && (diap == 6'd41) && (note == 9'd503) && (c_addr == 7'd11));
  cover property (@(posedge clk) started && (diap == 6'd42) && (note == 9'd504) && (c_addr == 7'd0));
  cover property (@(posedge clk) started && (diap == 6'd42) && (note == 9'd511) && (c_addr == 7'd7));

  cover property (@(posedge clk) started && (note == 9'd11) && (c_addr == 7'd11));
  cover property (@(posedge clk) started && (note == 9'd12) && (c_addr == 7'd0) && (diap == 6'd1));

  // Cover divider truncation region (indicates loss due to 4-bit divider)
  cover property (@(posedge clk) started && ((6'd42 - diap) >= 6'd16));

  // Output zero/non-zero hit
  cover property (@(posedge clk) started && (adder == 32'd0));
  cover property (@(posedge clk) started && (adder != 32'd0));

endmodule

// Bind to the DUT type (internal signals connected explicitly)
bind note2dds note2dds_sva u_note2dds_sva (
  .clk      (clk),
  .note     (note),
  .adder    (adder),
  .addr     (addr),
  .divider  (divider),
  .adder_tbl(adder_tbl),
  .diap     (diap),
  .c_addr   (c_addr)
);