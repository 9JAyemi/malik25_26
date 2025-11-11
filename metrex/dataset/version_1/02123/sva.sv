// SVA for the provided DUTs (bindable, concise, quality-focused)

// Reverse byte order: checks and key coverage
module reverse_byte_order_sva;
  // Bound into reverse_byte_order scope; can see in/out
  always @* begin
    if (!$isunknown(in)) begin
      assert (out == {in[7:0], in[15:8], in[23:16], in[31:24]})
        else $error("reverse_byte_order: out mismatch");
    end
    // Simple functional coverage
    cover (in == 32'h00000000 && out == 32'h00000000);
    cover (in == 32'hFFFFFFFF && out == 32'hFFFFFFFF);
    cover (in == 32'h01234567 && out == 32'h67452301);
    cover (in[31:24] == 8'hA5 && out[7:0]  == 8'hA5);   // MSB->LSB byte move
    cover (in[7:0]   == 8'h3C && out[31:24] == 8'h3C);  // LSB->MSB byte move
  end
endmodule

// Full adder: arithmetic and Boolean forms + full input coverage
module full_adder_sva;
  // Bound into full_adder; can see a,b,cin,sum,cout
  always @* begin
    if (!$isunknown({a,b,cin})) begin
      assert ({cout,sum} == a + b + cin)
        else $error("full_adder: arithmetic mismatch");
      assert (sum == (a ^ b ^ cin))
        else $error("full_adder: sum XOR form mismatch");
      assert (cout == ((a & b) | (a & cin) | (b & cin)))
        else $error("full_adder: cout majority form mismatch");
    end
    // Cover all 8 input combinations
    cover ({a,b,cin} == 3'b000);
    cover ({a,b,cin} == 3'b001);
    cover ({a,b,cin} == 3'b010);
    cover ({a,b,cin} == 3'b011);
    cover ({a,b,cin} == 3'b100);
    cover ({a,b,cin} == 3'b101);
    cover ({a,b,cin} == 3'b110);
    cover ({a,b,cin} == 3'b111);
  end
endmodule

// 4-bit adder with carry in: end-to-end arithmetic and key corner coverage
module adder_with_carry_in_sva;
  // Bound into adder_with_carry_in; can see a,b,cin,sum
  always @* begin
    if (!$isunknown({a,b,cin})) begin
      assert (sum == ({1'b0,a} + {1'b0,b} + cin))
        else $error("adder_with_carry_in: sum mismatch");
    end
    // Key coverage points
    cover (sum[4] == 1'b1);   // carry-out
    cover (sum == 5'd0);      // zero result
    cover (sum == 5'd31);     // max result
  end
endmodule

// Top-level end-to-end checks: transformation and placement
module top_module_sva;
  // Bound into top_module; can see in1,in2,cin,out, rev_in1,rev_in2,sum
  logic [4:0]  expected_sum;
  logic [31:0] expected_out;

  always @* begin
    expected_sum = {1'b0, in1[27:24]} + {1'b0, in2[27:24]} + cin;
    expected_out = 32'h0;
    expected_out[7]   = expected_sum[4];
    expected_out[6:3] = expected_sum[3:0];

    if (!$isunknown({in1,in2,cin})) begin
      // End-to-end behavior
      assert (out == expected_out)
        else $error("top_module: end-to-end out mismatch");

      // Byte reversals used internally
      assert (rev_in1 == {in1[7:0],  in1[15:8], in1[23:16], in1[31:24]})
        else $error("top_module: rev_in1 mismatch");
      assert (rev_in2 == {in2[7:0],  in2[15:8], in2[23:16], in2[31:24]})
        else $error("top_module: rev_in2 mismatch");

      // Nibble alignment through byte-reverse
      assert (rev_in1[3:0] == in1[27:24])
        else $error("top_module: rev_in1[3:0] alignment mismatch");
      assert (rev_in2[3:0] == in2[27:24])
        else $error("top_module: rev_in2[3:0] alignment mismatch");

      // Output bitfield placement from sum
      assert ({out[7],out[6:3]} == sum)
        else $error("top_module: sum placement mismatch");
      assert (out[31:8] == 24'h0 && out[2:0] == 3'b000)
        else $error("top_module: zero padding mismatch");
    end

    // Functional coverage of top scenarios
    cover (cin == 1'b0 && expected_sum[4] == 1'b0); // no carry
    cover (cin == 1'b1 && expected_sum[4] == 1'b1); // carry with cin
    cover (in1[27:24] == 4'h0 && in2[27:24] == 4'h0 && cin == 1'b0);
    cover (in1[27:24] == 4'hF && in2[27:24] == 4'hF && cin == 1'b1);
  end
endmodule

// Bind assertions into DUTs
bind reverse_byte_order    reverse_byte_order_sva rbo_chk();
bind full_adder            full_adder_sva         fa_chk();
bind adder_with_carry_in   adder_with_carry_in_sva awci_chk();
bind top_module            top_module_sva         top_chk();