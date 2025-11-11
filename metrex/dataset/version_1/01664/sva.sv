// SVA for shift_mux_xor
// Bind this file; focuses on correctness, X-safety, and minimal full coverage.

module shift_mux_xor_sva;
  // Bound into shift_mux_xor; has visibility of its internal signals.
  // Clocking and past-valid
  bit past_valid;
  initial past_valid = 0;
  always @(posedge clk) past_valid <= 1'b1;
  default clocking cb @(posedge clk); endclocking
  default disable iff (!past_valid);

  // Helpful local wires
  wire [7:0] taps = {shift_reg[255],shift_reg[127],shift_reg[63],shift_reg[31],
                     shift_reg[15],shift_reg[7],shift_reg[3],shift_reg[1]};

  // 1) Shift register behavior (X-safe)
  assert property (!$isunknown({$past(shift_reg[254:0]), $past(in[0])})
                   |-> shift_reg == {$past(shift_reg[254:0]), $past(in[0])})
    else $error("Shift behavior mismatch");

  // 2) 3-bit counter increments modulo-8 (X-safe on past)
  assert property (!$isunknown($past(counter)) |-> counter == $past(counter) + 3'd1)
    else $error("Counter did not increment by 1");

  // 3) Mux inputs are fixed one-hot constants, and stable
  genvar i;
  generate for (i=0;i<8;i++) begin : G_CONST
    assert property (mux_inputs[i] == (8'h1 << i))
      else $error("mux_inputs[%0d] constant mismatch", i);
  end endgenerate

  // 4) Mux selection matches counter; output one-hot
  assert property (mux_output == mux_inputs[counter])
    else $error("Mux output not matching selection");
  assert property ($onehot(mux_output))
    else $error("Mux output not one-hot");

  // 5) xor_input mapping and zero-extension
  assert property ({xor_input[7:0]} == taps)
    else $error("xor_input[7:0] mapping mismatch");
  assert property (xor_input[255:8] == '0)
    else $error("xor_input upper bits not zero");

  // 6) q is parity of taps and width-consistent (upper bits zero)
  assert property (!$isunknown(taps) |-> (q[0] == ^taps))
    else $error("q[0] parity mismatch");
  assert property (q[7:1] == '0)
    else $error("q[7:1] not zero");

  // 7) Minimal functional coverage
  //    - Observe a full counter cycle 0..7
  cover property (counter==3'd0 ##1 counter==3'd1 ##1 counter==3'd2 ##1 counter==3'd3
                  ##1 counter==3'd4 ##1 counter==3'd5 ##1 counter==3'd6 ##1 counter==3'd7);
  //    - See each mux selection value
  generate for (i=0;i<8;i++) begin : G_COV_SEL
    cover property (counter==i && $onehot(mux_output));
  end endgenerate
  //    - Observe both parity outcomes on q[0]
  cover property (q[0]==1'b0 ##1 q[0]==1'b1);
endmodule

bind shift_mux_xor shift_mux_xor_sva sva_inst();