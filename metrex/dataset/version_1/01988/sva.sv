// SVA for clockdivider
// Bind these assertions to the DUT.

module clockdivider_sva
  #(parameter int MAX1 = 50_000_000,
            int MAX2 = 500_000,
            int MID2 = 250_000)
(
  input  logic        clk,
  input  logic        rst,
  input  logic        select,
  input  logic [31:0] OUT1,
  input  logic [31:0] OUT2,
  input  logic        clkdivided1hz,
  input  logic        clkdivided200hz,
  input  logic        clkselect
);

  // Reset behavior (no disable iff here; we want to check reset effect)
  // On any clock where rst is 1, counters read as 0.
  a_rst_clears: assert property (@(posedge clk) rst |-> (OUT1==0 && OUT2==0));
  a_rst_hold0:  assert property (@(posedge clk) rst |=> (OUT1==0 && OUT2==0));

  // Common helpers
  function automatic bit past_ok(); return !$past(rst,1); endfunction

  // OUT1 counter: 0..MAX1 then wrap to 0
  a_out1_in_range: assert property (@(posedge clk) disable iff (rst) (OUT1 <= MAX1));
  a_out1_inc:      assert property (@(posedge clk) disable iff (rst)
                                   past_ok() && ($past(OUT1) < MAX1) |-> (OUT1 == $past(OUT1)+1));
  a_out1_wrap:     assert property (@(posedge clk) disable iff (rst)
                                   past_ok() && ($past(OUT1) == MAX1) |-> (OUT1 == 0));

  // 1 Hz pulse derived from OUT1 == MAX1, single-cycle, aligned neighbors
  a_1hz_eq:        assert property (@(posedge clk) (clkdivided1hz == (OUT1 == MAX1)));
  a_1hz_onecycle:  assert property (@(posedge clk) disable iff (rst) (clkdivided1hz |=> !clkdivided1hz));
  a_1hz_prev:      assert property (@(posedge clk) disable iff (rst)
                                   clkdivided1hz |-> $past(OUT1)==(MAX1-1));
  a_1hz_nextwrap:  assert property (@(posedge clk) disable iff (rst)
                                   clkdivided1hz |=> OUT1==0);

  // OUT2 counter: 0..MAX2 then wrap to 0
  a_out2_in_range: assert property (@(posedge clk) disable iff (rst) (OUT2 <= MAX2));
  a_out2_inc:      assert property (@(posedge clk) disable iff (rst)
                                   past_ok() && ($past(OUT2) < MAX2) |-> (OUT2 == $past(OUT2)+1));
  a_out2_wrap:     assert property (@(posedge clk) disable iff (rst)
                                   past_ok() && ($past(OUT2) == MAX2) |-> (OUT2 == 0));

  // 200 Hz pulse at midpoint of OUT2 count, single-cycle, aligned neighbors
  a_200hz_eq:       assert property (@(posedge clk) (clkdivided200hz == (OUT2 == MID2)));
  a_200hz_onecycle: assert property (@(posedge clk) disable iff (rst) (clkdivided200hz |=> !clkdivided200hz));
  a_200hz_prev:     assert property (@(posedge clk) disable iff (rst)
                                    clkdivided200hz |-> $past(OUT2)==(MID2-1));
  a_200hz_next:     assert property (@(posedge clk) disable iff (rst)
                                    clkdivided200hz |=> OUT2==(MID2+1));

  // clkselect mapping
  a_select_map:    assert property (@(posedge clk) (clkselect == clkdivided200hz));

  // Minimal functional coverage
  c_out1_wrap:     cover property (@(posedge clk) disable iff (rst)
                                   (OUT1==MAX1) ##1 (OUT1==0));
  c_out2_mid:      cover property (@(posedge clk) disable iff (rst)
                                   (OUT2==MID2-1) ##1 (OUT2==MID2) ##1 (OUT2==MID2+1));
  c_out2_wrap:     cover property (@(posedge clk) disable iff (rst)
                                   (OUT2==MAX2) ##1 (OUT2==0));
  c_1hz_pulse:     cover property (@(posedge clk) disable iff (rst) clkdivided1hz);
  c_200hz_pulse:   cover property (@(posedge clk) disable iff (rst) clkdivided200hz);
  c_clkselect:     cover property (@(posedge clk) disable iff (rst) clkselect);

endmodule

// Bind into the DUT
bind clockdivider clockdivider_sva
  #(.MAX1(50_000_000), .MAX2(500_000), .MID2(250_000))
  clockdivider_sva_i (
    .clk(clk),
    .rst(rst),
    .select(select),
    .OUT1(OUT1),
    .OUT2(OUT2),
    .clkdivided1hz(clkdivided1hz),
    .clkdivided200hz(clkdivided200hz),
    .clkselect(clkselect)
  );