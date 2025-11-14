// SVA for module spi
// Bind into the DUT to check key behavior concisely while providing high-quality coverage.

bind spi spi_sva #(.N(N), .tope(tope)) spi_sva_i();

module spi_sva #(parameter int N=8, parameter int tope=500);
  // This bind module relies on being instantiated into spi scope; it references DUT signals directly.

  default clocking cb @(posedge clk); endclocking
  default disable iff (reset);

  // Reset brings design to known idle state (mosi is intentionally excluded; RTL does not reset it)
  assert property (reset |=> countd==0 && sclk==0 && run==0 && div==0 && ss==1 && done==0
                             && dataout==0 && datase==0 && datare==0);

  // Idle (en==0) state each cycle and next-cycle loads
  assert property (!en |=> countd==0 && sclk==0 && run==0 && div==0 && ss==1 && done==0);
  assert property (!en |=> datase==$past(datain));
  assert property (!en |=> mosi==$past(datase[N-1]));

  // Enable/start handshake
  assert property ($rose(en) |=> run==1 && ss==0 && !done);

  // Divider and SCLK behavior while actively running a transfer
  assert property (en && run && !done && (div!=tope) |=> div==$past(div)+1 && sclk==$past(sclk));
  assert property (en && run && !done && (div==tope) |=> div==0 && sclk!=$past(sclk));

  // Falling-edge actions (sclk was 1 before toggle): bit count, mosi drive, done on last bit
  assert property (en && run && !done && (div==tope) && $past(sclk)
                   |=> mosi==$past(datase[N-1])
                       && countd==($past(countd)==(N-1) ? 0 : $past(countd)+1)
                       && done==($past(countd)==(N-1)));

  // Rising-edge actions (sclk was 0 before toggle): sample MISO, shift both shift-registers
  assert property (en && run && !done && (div==tope) && !$past(sclk)
                   |=> datare==={$past(miso), $past(datare[N-1:1])}
                       && datase==={$past(datase[N-2:0]), 1'b1});

  // After done while still enabled: stop running, freeze sclk, update dataout from datare
  assert property (en && done |=> run==0 && dataout==$past(datare));
  assert property (en && done |-> $stable(sclk));

  // SS mirrors enable (one-cycle latency due to sequential assignment)
  assert property ( en |=> ss==0);
  assert property (!en |=> ss==1);

  // Ranges/sanity
  assert property (en && run && !done |-> (div>=0 && div<=tope));
  assert property (en && run && !done |-> (countd>=0 && countd<= (N-1)));

  // MOSI only changes on the falling-edge update during an active transfer
  assert property (en && run && !done && $changed(mosi)
                   |-> $past(div==tope && sclk));

  // Dataout only changes on the done path (exclude reset)
  assert property (!reset && $changed(dataout) |-> $past(en && done));

  // -----------------------
  // Coverage
  // -----------------------
  // A complete transfer from enable to done
  cover property ($rose(en) ##[1:$] done);

  // Observe both sclk edge types during active transfer
  cover property (en && run && !done && div==tope &&  $past(sclk));
  cover property (en && run && !done && div==tope && !$past(sclk));

  // Capture at least one miso==0 and one miso==1 sample during rising-edge capture
  cover property (en && run && !done && div==tope && !$past(sclk) && ($past(miso)==1'b0));
  cover property (en && run && !done && div==tope && !$past(sclk) && ($past(miso)==1'b1));

  // Dataout update observed
  cover property (en && done ##1 (dataout==$past(datare)));

endmodule