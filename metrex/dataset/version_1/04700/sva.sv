// SVA for min_finder/prioritiy_encoder/decoder
// Bind this file alongside the DUT

module min_finder_sva (min_finder dut);

  // Combinational checks guarded against X/Z on inputs
  always @* begin
    if (!$isunknown({dut.a,dut.b,dut.c,dut.d})) begin
      // Structural wiring check (exposes truncation of the 16-bit concat to 4 bits)
      assert (dut.inputs == dut.d[3:0])
        else $error("inputs is not the 4x4b concat; it equals d[3:0] due to truncation");

      // Priority encoder behavior (as coded)
      assert ((dut.inputs[0]==1'b0) ? (dut.encoded==2'b01) : 1'b1)
        else $error("pe: when inputs[0]==0, encoded must be 01");
      assert ((dut.inputs[0]==1'b1 && dut.inputs[1]==1'b0) ? (dut.encoded==2'b10) : 1'b1)
        else $error("pe: when inputs[1]==0 (and inputs[0]==1), encoded must be 10");
      assert ((dut.inputs[0]==1'b1 && dut.inputs[1]==1'b1 && (dut.inputs[2] <= dut.inputs[3])) ? (dut.encoded==2'b11) : 1'b1)
        else $error("pe: when inputs[2]<=inputs[3] (and inputs[0]==inputs[1]==1), encoded must be 11");
      assert ((dut.inputs[0]==1'b1 && dut.inputs[1]==1'b1 && (dut.inputs[2] > dut.inputs[3])) ? (dut.encoded==2'b00) : 1'b1)
        else $error("pe: when inputs[2]>inputs[3] (and inputs[0]==inputs[1]==1), encoded must be 00");

      // Decoder mapping
      assert (dut.min == ((dut.encoded==2'b01) ? 8'b0000_0001
                             : (dut.encoded==2'b10) ? 8'b0000_0010
                             : (dut.encoded==2'b11) ? 8'b0000_0100
                             : 8'b0000_0000))
        else $error("decoder output not consistent with encoded");

      // High-level spec: choose min of the 4 LSB nibbles with tie-breaker A>B>C>D
      automatic logic [7:0] exp_min;
      if      ((dut.a[3:0] <= dut.b[3:0]) && (dut.a[3:0] <= dut.c[3:0]) && (dut.a[3:0] <= dut.d[3:0])) exp_min = 8'b0000_0001;
      else if ((dut.b[3:0] <= dut.c[3:0]) && (dut.b[3:0] <= dut.d[3:0]))                                   exp_min = 8'b0000_0010;
      else if ((dut.c[3:0] <= dut.d[3:0]))                                                                  exp_min = 8'b0000_0100;
      else                                                                                                  exp_min = 8'b0000_1000;

      assert (dut.min == exp_min)
        else $error("Top-level min one-hot does not reflect min(a[3:0],b[3:0],c[3:0],d[3:0]) with A>B>C>D tie-breaker");

      // Sanity: one-hot result expected at top level
      assert ($onehot(exp_min)) else $error("Expected one-hot result");
      assert ($onehot(dut.min)) else $error("min should be one-hot");
    end
  end

  // Functional coverage
  // Cover each selected winner at the spec level
  cover property ( (dut.a[3:0] <= dut.b[3:0]) && (dut.a[3:0] <= dut.c[3:0]) && (dut.a[3:0] <= dut.d[3:0]) && dut.min==8'b0000_0001 );
  cover property ( (dut.b[3:0] <= dut.c[3:0]) && (dut.b[3:0] <= dut.d[3:0]) && dut.min==8'b0000_0010 );
  cover property ( (dut.c[3:0] <= dut.d[3:0]) && dut.min==8'b0000_0100 );
  cover property ( (dut.a[3:0] > dut.b[3:0]) && (dut.b[3:0] > dut.c[3:0]) && (dut.c[3:0] > dut.d[3:0]) && dut.min==8'b0000_1000 ); // exposes missing decode for D

  // Tie-break coverage
  cover property ( (dut.a[3:0] == dut.b[3:0]) && (dut.a[3:0] <= dut.c[3:0]) && (dut.a[3:0] <= dut.d[3:0]) && dut.min==8'b0000_0001 );
  cover property ( (dut.b[3:0] == dut.c[3:0]) && (dut.b[3:0] <= dut.a[3:0]) && (dut.b[3:0] <= dut.d[3:0]) && dut.min==8'b0000_0010 );
  cover property ( (dut.c[3:0] == dut.d[3:0]) && (dut.c[3:0] <= dut.a[3:0]) && (dut.c[3:0] <= dut.b[3:0]) && dut.min==8'b0000_0100 );

  // Encoder corner: only case producing encoded==2'b00 in current logic
  cover property ( dut.inputs==4'b1110 && dut.encoded==2'b00 && dut.min==8'b0000_0000 );

endmodule

bind min_finder min_finder_sva mfsva(.dut(this));