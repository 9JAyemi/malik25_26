// SVA for Display. Bind this module to the DUT.
module Display_sva;
  default clocking cb @(posedge clk); endclocking

  // past_valid to guard $past()
  logic past_valid; initial past_valid = 1'b0; always @(posedge clk) past_valid <= 1'b1;
  default disable iff (!past_valid);

  // Initial state from DUT's initial block
  assert property ($initstate |-> tmp==4'b0111 && counter==16'd0 && flash_counter==32'd0 && flash_state==1'b0);

  // tmp legal values at clock boundaries
  assert property (tmp inside {4'b0111,4'b1011,4'b1101,4'b1110});

  // Next tmp function
  function automatic [3:0] next_tmp(input [3:0] t);
    case (t)
      4'b0111: next_tmp = 4'b1011;
      4'b1011: next_tmp = 4'b1101;
      4'b1101: next_tmp = 4'b1110;
      4'b1110: next_tmp = 4'b0111;
      default: next_tmp = 4'b0111;
    endcase
  endfunction

  // counter behavior and tmp update only on wrap
  assert property ($past(counter)==MAX_COUNTER |-> counter==16'd0 && tmp==next_tmp($past(tmp)));
  assert property ($past(counter)!=MAX_COUNTER |-> counter==$past(counter)+16'd1 && tmp==$past(tmp));
  assert property (counter<=MAX_COUNTER);

  // flash_counter behavior and flash_state toggle only on wrap
  assert property ($past(flash_counter)==MAX_FLASH_COUNTER |-> flash_counter==32'd0 && flash_state==~$past(flash_state));
  assert property ($past(flash_counter)!=MAX_FLASH_COUNTER |-> flash_counter==$past(flash_counter)+32'd1 && flash_state==$past(flash_state));
  assert property (flash_counter<=MAX_FLASH_COUNTER);

  // an mapping
  assert property (!flash_state |-> an==tmp && $onehot0(an));
  assert property ( flash_state |-> an==(tmp | flash));

  // Selected nibble and 7-seg encoding mapping
  function automatic [3:0] sel_nib;
    case (tmp)
      4'b0111: sel_nib = num[15:12];
      4'b1011: sel_nib = num[11:8];
      4'b1101: sel_nib = num[7:4];
      4'b1110: sel_nib = num[3:0];
      default: sel_nib = 4'hx;
    endcase
  endfunction
  function automatic [7:0] seg_enc(input [3:0] n);
    case (n)
      4'h0: seg_enc = 8'b0000_0011;
      4'h1: seg_enc = 8'b1001_1111;
      4'h2: seg_enc = 8'b0010_0101;
      4'h3: seg_enc = 8'b0000_1101;
      4'h4: seg_enc = 8'b1001_1001;
      4'h5: seg_enc = 8'b0100_1001;
      4'h6: seg_enc = 8'b0100_0001;
      4'h7: seg_enc = 8'b0001_1111;
      4'h8: seg_enc = 8'b0000_0001;
      4'h9: seg_enc = 8'b0000_1001;
      default: seg_enc = 8'hxx;
    endcase
  endfunction

  // When selected nibble is 0..9, display must match encoding
  assert property (sel_nib<=4'd9 |-> display==seg_enc(sel_nib));

  // Outputs not X/Z
  assert property (!$isunknown(an) && !$isunknown(display));

  // Cover: full digit rotation across wraps
  cover property (tmp==4'b0111 ##[1:$] tmp==4'b1011 ##[1:$] tmp==4'b1101 ##[1:$] tmp==4'b1110 ##[1:$] tmp==4'b0111);

  // Cover: flash_state toggles
  cover property (flash_state ##[1:$] !flash_state ##[1:$] flash_state);

  // Cover: observe each decimal code appear
  genvar d;
  generate
    for (d=0; d<=9; d++) begin : CODES
      cover property (sel_nib==d && display==seg_enc(d));
    end
  endgenerate
endmodule

bind Display Display_sva sva_inst();