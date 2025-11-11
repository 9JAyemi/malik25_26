// SVA for BCD_to_Binary
// Bind this module to the DUT for assertion/coverage

module BCD_to_Binary_sva (
  input logic [3:0] bcd_in,
  input logic [7:0] bin_out
);

  // Golden model
  function automatic logic [7:0] exp_bin(input logic [3:0] b);
    case (b)
      4'd0: exp_bin = 8'h00;
      4'd1: exp_bin = 8'h01;
      4'd2: exp_bin = 8'h02;
      4'd3: exp_bin = 8'h03;
      4'd4: exp_bin = 8'h04;
      4'd5: exp_bin = 8'h05;
      4'd6: exp_bin = 8'h06;
      4'd7: exp_bin = 8'h07;
      4'd8: exp_bin = 8'h08;
      4'd9: exp_bin = 8'h09;
      default: exp_bin = 8'h00;
    endcase
  endfunction

  // Immediate functional equivalence and sanity
  always_comb begin
    assert (bin_out === exp_bin(bcd_in))
      else $error("BCD_to_Binary mismatch: bcd_in=%0d bin_out=0x%0h exp=0x%0h", bcd_in, bin_out, exp_bin(bcd_in));
    assert (bin_out[7:4] == 4'h0)
      else $error("BCD_to_Binary high nibble not zero: bin_out=0x%0h", bin_out);
    if (!$isunknown(bcd_in) && (bcd_in <= 4'd9))
      assert (bin_out == {4'h0, bcd_in})
        else $error("BCD_to_Binary legal mapping wrong: bcd_in=%0d bin_out=0x%0h", bcd_in, bin_out);
    if ($isunknown(bcd_in) || (bcd_in > 4'd9))
      assert (bin_out == 8'h00)
        else $error("BCD_to_Binary illegal/unknown input must map to 0: bcd_in=%b bin_out=0x%0h", bcd_in, bin_out);
  end

  // Clockless concurrent properties driven by input-change event
  event ev_bcd_change;
  always @(bcd_in) -> ev_bcd_change;

  // Zero-cycle combinational response
  property p_comb_resp;
    @(ev_bcd_change) 1 |-> (bin_out == exp_bin(bcd_in));
  endproperty
  assert property (p_comb_resp);

  // No X/Z on output for known legal inputs
  property p_no_x_on_legal;
    @(ev_bcd_change) (!$isunknown(bcd_in) && (bcd_in <= 4'd9)) |-> (!$isunknown(bin_out));
  endproperty
  assert property (p_no_x_on_legal);

  // Functional coverage
  cover property (@(ev_bcd_change) (bcd_in==4'd0 && bin_out==8'h00));
  cover property (@(ev_bcd_change) (bcd_in==4'd1 && bin_out==8'h01));
  cover property (@(ev_bcd_change) (bcd_in==4'd2 && bin_out==8'h02));
  cover property (@(ev_bcd_change) (bcd_in==4'd3 && bin_out==8'h03));
  cover property (@(ev_bcd_change) (bcd_in==4'd4 && bin_out==8'h04));
  cover property (@(ev_bcd_change) (bcd_in==4'd5 && bin_out==8'h05));
  cover property (@(ev_bcd_change) (bcd_in==4'd6 && bin_out==8'h06));
  cover property (@(ev_bcd_change) (bcd_in==4'd7 && bin_out==8'h07));
  cover property (@(ev_bcd_change) (bcd_in==4'd8 && bin_out==8'h08));
  cover property (@(ev_bcd_change) (bcd_in==4'd9 && bin_out==8'h09));
  cover property (@(ev_bcd_change) (bcd_in>4'd9 && bin_out==8'h00));
  cover property (@(ev_bcd_change) ($isunknown(bcd_in) && bin_out==8'h00));

endmodule

bind BCD_to_Binary BCD_to_Binary_sva sva(.bcd_in(bcd_in), .bin_out(bin_out));