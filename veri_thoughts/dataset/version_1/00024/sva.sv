// SVA: bindable checkers for the given DUTs (concise, high-quality)

module priority_encoder_sva (input [7:0] in, input [2:0] pos);
  // Map checks for valid one-hot[6:0]
  genvar i;
  generate
    for (i=0; i<7; i++) begin : enc_map
      always_comb begin
        if (!$isunknown({in,pos}) && in == (8'b1 << i)) assert (pos == i[2:0]);
        cover (in == (8'b1 << i) && pos == i[2:0]);
      end
    end
  endgenerate

  // Default path (all other patterns) -> 3'b111
  wire valid_onehot7 = $onehot(in[6:0]) && !in[7];
  always_comb begin
    if (!$isunknown({in,pos}) && !valid_onehot7) assert (pos == 3'b111);
    cover (!valid_onehot7 && pos == 3'b111);
    // Representative default covers
    cover (in == 8'b0000_0000 && pos == 3'b111);
    cover (in == 8'b1000_0000 && pos == 3'b111);
    cover ($countones(in) > 1 && pos == 3'b111);
  end
endmodule

module adder_sva (input [2:0] a, input [2:0] b, input [2:0] sum);
  always_comb begin
    if (!$isunknown({a,b,sum})) assert (sum === ((a - b) & 3'b111));
    // Key scenarios
    cover (a == b && sum == 3'b000);
    cover (a == 3'b000 && b == 3'b001 && sum == 3'b111); // wrap underflow
    cover (a == 3'b111 && b == 3'b001 && sum == 3'b110);
  end
endmodule

module top_module_sva (input [7:0] in1, input [7:0] in2, input [2:0] pos_diff);
  function automatic [2:0] enc7 (input [7:0] x);
    case (x)
      8'b0000_0001: enc7 = 3'b000;
      8'b0000_0010: enc7 = 3'b001;
      8'b0000_0100: enc7 = 3'b010;
      8'b0000_1000: enc7 = 3'b011;
      8'b0001_0000: enc7 = 3'b100;
      8'b0010_0000: enc7 = 3'b101;
      8'b0100_0000: enc7 = 3'b110;
      default:       enc7 = 3'b111;
    endcase
  endfunction

  always_comb begin
    if (!$isunknown({in1,in2,pos_diff})) assert (pos_diff === ((enc7(in1) - enc7(in2)) & 3'b111));
    // Top-level scenarios
    cover (in1==8'b0000_0001 && in2==8'b0000_0001 && pos_diff==3'b000); // equal -> 0
    cover (in1==8'b0000_0001 && in2==8'b0000_0010 && pos_diff==3'b111); // wrap
    cover (in1==8'b0100_0000 && in2==8'b0000_0001 && pos_diff==3'b101);
    cover (in1==8'b1000_0000 && in2==8'b0000_0000 && pos_diff==3'b000); // both invalid -> 7-7
    cover (in1==8'b1000_0000 && in2==8'b0000_0001 && pos_diff==((3'b111-3'b001)&3'b111)); // invalid-valid
  end
endmodule

// Binds
bind priority_encoder priority_encoder_sva(.in(in), .pos(pos));
bind adder            adder_sva(.a(a), .b(b), .sum(sum));
bind top_module       top_module_sva(.in1(in1), .in2(in2), .pos_diff(pos_diff));