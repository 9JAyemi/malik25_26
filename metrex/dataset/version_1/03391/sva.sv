// SVA for psdos
module psdos_sva;
  default clocking cb @(posedge CLKOUT); endclocking

  // Start detection drives init next cycle
  assert property ((!Rx && (i==0)) |=> init);

  // Init can only rise due to start condition
  assert property ((init && !$past(init)) |-> (!$past(Rx) && ($past(i)==0)));

  // i progression while in frame, and reset after 9
  assert property ((init && (i<9)) |=> i == $past(i)+1);
  assert property ((i==9) |=> (i==0) && !init);

  // i must be 0 when not in frame
  assert property ((!init) |-> (i==0));

  // j accumulates ones for data bits only (i<8), holds at i==8, resets at decision
  assert property ((init && (i<8) && Rx)  |-> j == $past(j)+1);
  assert property ((init && (i<8) && !Rx) |-> j == $past(j));
  assert property ((init && (i==8))       |-> j == $past(j));
  assert property ((i==9)                 |-> j == 0);

  // Bounds/sanity
  assert property (i <= 9);
  assert property (j <= 8);
  assert property ((i==9) |-> !$isunknown({DONE,Rx_error,DATA}));

  // Parity check and outputs on decision cycle
  // Use $past(j[0]) because j is cleared in the same cycle
  assert property (
    (i==9) |->
      (Rx_error == (regis[8] == $past(j[0])))
      && (DONE == ~Rx_error)
      && (Rx_error ? (DATA==8'h00) : (DATA==regis[7:0]))
  );

  // Coverage
  cover property ((!Rx && (i==0)) ##1 init ##[1:8] (i==9 && !Rx_error && DONE));
  cover property ((!Rx && (i==0)) ##1 init ##[1:8] (i==9 && Rx_error && !DONE));
endmodule

bind psdos psdos_sva psdos_sva_inst();