// SVA for comparator_decoder
// Bind into DUT; accesses internal nets by name
module comparator_decoder_sva;

  default clocking cb @(posedge clk); endclocking

  // Comparator correctness (when inputs are known)
  assert property ( !$isunknown({a,b})
                    |-> (eq == (a==b)) && (gt == (a>b)) && (lt == (a<b)) && $onehot({eq,gt,lt}) );

  // Decoder mapping is exact
  assert property (decoder_out[0] == lt);
  assert property (decoder_out[1] == gt);
  assert property (decoder_out[2] == eq);
  assert property (decoder_out[5:3] == 3'b000 && decoder_out[15:6] == '0);

  // Asynchronous reset drives reg_out to 0 immediately
  assert property (@(posedge reset) reg_out == 16'h0000);

  // Register update/hold and enable-only updates
  assert property (disable iff (reset) decoder_out[sel] |=> reg_out == $past(reg_in));
  assert property (disable iff (reset) !decoder_out[sel] |=> reg_out == $past(reg_out));
  assert property (disable iff (reset) $changed(reg_out) |-> decoder_out[sel]);

  // Output mux behavior
  assert property (decoder_out[sel] |-> out == reg_out);
  assert property (!decoder_out[sel] |-> out == {12'h000, 1'b0, eq, gt, lt});

  // Optional: sel>=3 never enables write
  assert property ( (sel inside {[3:15]}) |-> decoder_out[sel] == 1'b0 );

  // Coverage
  cover property (eq);
  cover property (gt);
  cover property (lt);
  cover property (decoder_out[sel]);           // write taken
  cover property (!decoder_out[sel]);          // mux comparator path
  cover property (decoder_out[sel] && mode==0);
  cover property (decoder_out[sel] && mode==1);
  cover property (sel==0 && lt);
  cover property (sel==1 && gt);
  cover property (sel==2 && eq);
  cover property (@(posedge reset) 1);

endmodule

bind comparator_decoder comparator_decoder_sva sva_i;