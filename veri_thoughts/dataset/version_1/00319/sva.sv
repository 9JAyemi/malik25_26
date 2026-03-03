// SVA checker for three_bit_adder
module three_bit_adder_sva (
  input A, B, Ci, S, Co,
  input n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11
);
  // Input-space and result coverage
  always_comb begin
    cover ({A,B,Ci} == 3'b000);
    cover ({A,B,Ci} == 3'b001);
    cover ({A,B,Ci} == 3'b010);
    cover ({A,B,Ci} == 3'b011);
    cover ({A,B,Ci} == 3'b100);
    cover ({A,B,Ci} == 3'b101);
    cover ({A,B,Ci} == 3'b110);
    cover ({A,B,Ci} == 3'b111);

    cover ({Co,S} == 2'b00);
    cover ({Co,S} == 2'b01);
    cover ({Co,S} == 2'b10);
    cover ({Co,S} == 2'b11);
  end

  // Combinational checks (guard against X/Z on inputs)
  always_comb begin
    if (!$isunknown({A,B,Ci})) begin
      // Outputs and key internal nets must be known when inputs are known
      assert (!$isunknown({S,Co,n1,n2,n3,n4,n5,n6,n7,n8,n9,n10,n11}));

      // Functional correctness (three equivalent forms)
      assert (S  === (A ^ B ^ Ci));
      assert (Co === ((A & B) | (A & Ci) | (B & Ci)));
      assert ({Co,S} === ({1'b0,A} + {1'b0,B} + {1'b0,Ci}));

      // Structural consistency with RTL
      assert (n1 === (A ^ B));
      assert (n2 === (A & B));
      assert (n3 === (n1 & Ci));
      assert (S  === (n1 ^ Ci));
      assert (Co === (n2 | n3));

      // Redundant internal network equivalences
      assert (n4  === (n2 & n3));
      assert (n7  === (n2 & n3));
      assert (n11 === (n2 & n3));
      assert (n8  === (n1 & Ci));
      assert (n3  === n8);

      assert (n5  === (n4 | n3));
      assert (n5  === n3);

      assert (n9  === (n7 | n8));
      assert (n9  === n3);

      assert (n6  === ~n5);
      assert (n6  === ~n3);

      assert (n10 === ~n9);
      assert (n10 === ~n3);
    end
  end
endmodule

// Bind the checker into every instance of the DUT
bind three_bit_adder three_bit_adder_sva sva (.*);