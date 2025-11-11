// SVA for Seven_seg: bindable checker focusing on correctness and essential coverage
module Seven_seg_sva (Seven_seg dut);

  // Default clock; selectively disable on reset for stateful checks
  default clocking cb @(posedge dut.clk); endclocking
  default disable iff (dut.reset);

  // Helper: 7-seg LUT function (same truth-table as DUT)
  function automatic [7:0] hex7seg(input logic [3:0] d);
    case (d)
      4'h0: hex7seg = 8'b11000000;
      4'h1: hex7seg = 8'b11111001;
      4'h2: hex7seg = 8'b10100100;
      4'h3: hex7seg = 8'b10110000;
      4'h4: hex7seg = 8'b10011001;
      4'h5: hex7seg = 8'b10010010;
      4'h6: hex7seg = 8'b10000010;
      4'h7: hex7seg = 8'b11111000;
      4'h8: hex7seg = 8'b10000000;
      4'h9: hex7seg = 8'b10010000;
      4'hA: hex7seg = 8'b10001000;
      4'hB: hex7seg = 8'b10000011;
      4'hC: hex7seg = 8'b11000110;
      4'hD: hex7seg = 8'b10100001;
      4'hE: hex7seg = 8'b10000110;
      4'hF: hex7seg = 8'b10001110;
    endcase
  endfunction

  // Basic coherency
  assert property (dut.ACK == dut.STB);
  assert property (dut.Segment == dut.digit_seg);
  assert property (dut.DAT_O  == dut.Segment);
  assert property (dut.scan   == dut.cnt[18:17]);
  assert property (!$isunknown({dut.AN, dut.Segment, dut.DAT_O, dut.ACK, dut.debug_data_hold}));

  // Counter must increment every clk (check even during reset)
  assert property (disable iff(1'b0) !$isunknown($past(dut.cnt)) |-> dut.cnt == $past(dut.cnt) + 32'd1);

  // data_hold reset and write/hold behavior
  always @(posedge dut.reset) assert (dut.data_hold == 16'h2333);
  assert property (dut.reset |-> dut.data_hold == 16'h2333);
  assert property (!dut.reset && dut.STB  |=> dut.data_hold == $past(dut.DAT_I));
  assert property (!dut.reset && !dut.STB |=> dut.data_hold == $past(dut.data_hold));
  assert property (dut.debug_data_hold == dut.data_hold);

  // Scan -> AN decode (one-cold pattern)
  assert property (dut.scan == 2'd0 |-> dut.AN == 4'b1110);
  assert property (dut.scan == 2'd1 |-> dut.AN == 4'b1101);
  assert property (dut.scan == 2'd2 |-> dut.AN == 4'b1011);
  assert property (dut.scan == 2'd3 |-> dut.AN == 4'b0111);
  assert property ($onehot(~dut.AN));

  // Scan -> digit nibble select; digit upper bits must be zero-extended
  assert property (dut.scan == 2'd0 |-> dut.digit[3:0] == dut.data_hold[3:0]   && dut.digit[7:4]==4'h0);
  assert property (dut.scan == 2'd1 |-> dut.digit[3:0] == dut.data_hold[7:4]   && dut.digit[7:4]==4'h0);
  assert property (dut.scan == 2'd2 |-> dut.digit[3:0] == dut.data_hold[11:8]  && dut.digit[7:4]==4'h0);
  assert property (dut.scan == 2'd3 |-> dut.digit[3:0] == dut.data_hold[15:12] && dut.digit[7:4]==4'h0);

  // 7-seg LUT correctness
  assert property (dut.digit_seg == hex7seg(dut.digit[3:0]));

  // Minimal, meaningful coverage

  // Scan cycles through all digits in order
  cover property (dut.scan==2'd0 ##1 dut.scan==2'd1 ##1 dut.scan==2'd2 ##1 dut.scan==2'd3);

  // Write handshake observed and updates visible on next cycle
  cover property (dut.STB ##1 dut.ACK && dut.data_hold == $past(dut.DAT_I));

  // Exercise all 16 hex encodings at least once
  genvar i;
  generate
    for (i=0; i<16; i++) begin : COV_LUT
      cover property (dut.digit[3:0] == i[3:0] && dut.digit_seg == hex7seg(i[3:0]));
    end
  endgenerate

endmodule

// Bind into all instances of Seven_seg
bind Seven_seg Seven_seg_sva Seven_seg_sva_b(.dut);