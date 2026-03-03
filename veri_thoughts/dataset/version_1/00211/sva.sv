// SVA checker for priority_encoder
// Focus: correctness for all input classes, X-propagation, concise full coverage
// synthesis translate_off
module priority_encoder_sva (input [3:0] I, input [1:0] O);

  // 2-state sanity
  always @* begin
    assert (!$isunknown(I)) else $error("priority_encoder: I has X/Z: %b", I);
    assert (!$isunknown(O)) else $error("priority_encoder: O has X/Z: %b", O);
  end

  // Functional checking (combinational)
  function automatic [1:0] enc4(input [3:0] i);
    unique case (1'b1)
      i[0]: enc4 = 2'b00;
      i[1]: enc4 = 2'b01;
      i[2]: enc4 = 2'b10;
      i[3]: enc4 = 2'b11;
      default: enc4 = 2'b00;
    endcase
  endfunction

  always @* if (!$isunknown(I)) begin
    if ($onehot(I)) begin
      assert (O == enc4(I))
        else $error("priority_encoder: onehot I=%b -> O=%b (exp=%b)", I, O, enc4(I));
    end else begin
      // zero or multi-hot must map to 2'b00 per RTL default
      assert (O == 2'b00)
        else $error("priority_encoder: non-onehot I=%b must produce O=00, got %b", I, O);
    end
  end

  // Minimal but complete functional coverage
  always @* begin
    cover (I == 4'b0000 && O == 2'b00);
    cover (I == 4'b0001 && O == 2'b00);
    cover (I == 4'b0010 && O == 2'b01);
    cover (I == 4'b0100 && O == 2'b10);
    cover (I == 4'b1000 && O == 2'b11);
    cover ((|I) && !$onehot(I) && O == 2'b00); // any multi-hot case
  end

endmodule

// Bind into DUT
bind priority_encoder priority_encoder_sva sva(.I(I), .O(O));
// synthesis translate_on