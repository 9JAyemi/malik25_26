// SVA for PS3spiControl
// Bind into DUT to access internal signals
module PS3spiControl_sva;
  default clocking @(posedge clk); endclocking

  // Counter and shifter behavior
  assert property (!cs_active |=> (bitcounter==3'b000 && $stable(inputbyte)));
  assert property (cs_active && !extclk_rising |=> ($stable(bitcounter) && $stable(inputbyte)));
  assert property (cs_active && extclk_rising |=> (bitcounter == ($past(bitcounter)+3'b001) && inputbyte == { $past(inputbyte[6:0]), $past(extdata_in)}));

  // byte_rec generation and pulse shape
  assert property ((cs_active && extclk_rising && (bitcounter==3'b111)) |=> byte_rec);
  assert property ($rose(byte_rec) |-> $past(cs_active && extclk_rising && (bitcounter==3'b111)));
  assert property (byte_rec |=> !byte_rec);

  // Allowed states and update gating
  assert property (bytestate inside {4'b0000,4'b0001,4'b0010});
  assert property (!byte_rec |=> $stable(bytestate));

  // Next-state mapping on a received byte
  assert property (byte_rec |=> (
      ($past(inputbyte[7]) && bytestate==4'b0001) ||
      (!$past(inputbyte[7]) && (
        ($past(bytestate)==4'b0000 && bytestate==4'b0001) ||
        ($past(bytestate)==4'b0001 && bytestate==4'b0010) ||
        ($past(bytestate)==4'b0010 && bytestate==4'b0000)
      ))
  ));

  // Keys1 update behavior: load only on byte_rec, correct bits per state, others stable
  // Effective state used during update is ($past(inputbyte[7]) ? 0 : $past(bytestate))
  assert property (byte_rec && ($past(inputbyte[7]) || ($past(bytestate)==4'b0000)) |=> (
      keys1[7]==$past(inputbyte[1]) &&
      keys1[6]==$past(inputbyte[2]) &&
      keys1[5]==$past(inputbyte[0]) &&
      keys1[4]==$past(inputbyte[3]) &&
      keys1[3]==$past(inputbyte[4]) &&
      $stable(keys1[2:0])
  ));
  assert property (byte_rec && !$past(inputbyte[7]) && ($past(bytestate)==4'b0001) |=> (
      keys1[1]==$past(inputbyte[2]) &&
      keys1[0]==$past(inputbyte[1]) &&
      $stable(keys1[7:2])
  ));
  assert property (byte_rec && !$past(inputbyte[7]) && ($past(bytestate)==4'b0010) |=> (
      keys1[2]==($past(inputbyte[0]) | $past(inputbyte[2])) &&
      $stable({keys1[7:3],keys1[1:0]})
  ));
  assert property (!byte_rec |=> $stable(keys1));

  // keys2 is never written after init => must remain stable
  assert property ($stable(keys2));

  // Coverage
  cover property ((cs_active && extclk_rising && (bitcounter==3'b111)) |=> byte_rec);                // end-of-byte
  cover property (byte_rec && $past(inputbyte[7]));                                                  // header/reset byte observed
  cover property (byte_rec ##1 (bytestate==4'b0001) ##1 byte_rec ##1 (bytestate==4'b0010) ##1 byte_rec ##1 (bytestate==4'b0000)); // 0->1->2->0 cycle
  cover property (byte_rec && !$past(inputbyte[7]) && ($past(bytestate)==4'b0010) && ($past(inputbyte[0] | inputbyte[2])==1));
  cover property (byte_rec && !$past(inputbyte[7]) && ($past(bytestate)==4'b0010) && ($past(inputbyte[0] | inputbyte[2])==0));
endmodule

bind PS3spiControl PS3spiControl_sva sva_i;