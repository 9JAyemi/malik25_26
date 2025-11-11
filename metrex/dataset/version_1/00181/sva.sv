// SVA for top_module, priority_encoder, and up_down_counter
// Concise, high-signal-coverage, with key functional checks and coverage

module top_module_sva (
  input logic        clk,
  input logic        reset,
  input logic [3:0]  inputs,
  input logic        up_down,
  input logic        load,
  input logic [3:0]  D,
  input logic [3:0]  Q,
  input logic [1:0]  priority_encoder_output
);

  // Priority encoder golden model
  function automatic logic [1:0] enc_expected (input logic [3:0] I);
    case (I)
      4'b0001: enc_expected = 2'b01;
      4'b0010: enc_expected = 2'b10;
      4'b0100: enc_expected = 2'b11;
      default: enc_expected = 2'b00;
    endcase
  endfunction

  // Sanity: no X on key outputs
  ap_no_x_q:      assert property (@(posedge clk) !$isunknown(Q));
  ap_no_x_enc_o:  assert property (@(posedge clk) !$isunknown(priority_encoder_output));

  // Priority encoder correctness (sampled on clk)
  ap_enc_correct: assert property (@(posedge clk) priority_encoder_output == enc_expected(inputs));

  // Counter behavior (synchronous reset > load > up/down increment/decrement)
  ap_cnt_reset:   assert property (@(posedge clk) reset |=> Q == 4'h0);
  ap_cnt_rst_over_load: assert property (@(posedge clk) reset && load |=> Q == 4'h0);

  ap_cnt_load:    assert property (@(posedge clk) !reset && load
                                              |=> Q == $past(D));

  ap_cnt_inc:     assert property (@(posedge clk) !reset && !load && up_down
                                              |=> Q == $past(Q) + 4'h1);

  ap_cnt_dec:     assert property (@(posedge clk) !reset && !load && !up_down
                                              |=> Q == $past(Q) - 4'h1);

  // Q must be stable between clocks (no glitches)
  ap_cnt_stable_between_clks: assert property (@(negedge clk) $stable(Q));

  // Functional coverage

  // Counter branch coverage
  cp_reset: cover property (@(posedge clk) reset);
  cp_load:  cover property (@(posedge clk) !reset && load);
  cp_inc:   cover property (@(posedge clk) !reset && !load && up_down);
  cp_dec:   cover property (@(posedge clk) !reset && !load && !up_down);

  // Counter wrap-around coverage
  cp_wrap_inc: cover property (@(posedge clk)
                               !reset && !load && up_down && $past(Q)==4'hF ##1 Q==4'h0);
  cp_wrap_dec: cover property (@(posedge clk)
                               !reset && !load && !up_down && $past(Q)==4'h0 ##1 Q==4'hF);

  // Encoder output coverage for all encodings
  cp_enc_01: cover property (@(posedge clk) inputs==4'b0001 && priority_encoder_output==2'b01);
  cp_enc_10: cover property (@(posedge clk) inputs==4'b0010 && priority_encoder_output==2'b10);
  cp_enc_11: cover property (@(posedge clk) inputs==4'b0100 && priority_encoder_output==2'b11);
  // Default branch examples (zero and multi-hot map to 00)
  cp_enc_00_zero:   cover property (@(posedge clk) inputs==4'b0000 && priority_encoder_output==2'b00);
  cp_enc_00_illegal:cover property (@(posedge clk) inputs inside {4'b1000,4'b0011,4'b1111}
                                                && priority_encoder_output==2'b00);

endmodule

// Bind into the DUT (has visibility of internal priority_encoder_output)
bind top_module top_module_sva sva_top (
  .clk(clk),
  .reset(reset),
  .inputs(inputs),
  .up_down(up_down),
  .load(load),
  .D(D),
  .Q(Q),
  .priority_encoder_output(priority_encoder_output)
);