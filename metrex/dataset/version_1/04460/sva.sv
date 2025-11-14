// SVA checker for distance_calculator
module distance_calculator_sva #(parameter int SCALE = 16) (
  input  signed [31:0] x1,
  input  signed [31:0] y1,
  input  signed [31:0] z1,
  input  signed [31:0] x2,
  input  signed [31:0] y2,
  input  signed [31:0] z2,
  input         [31:0] distance
);

  // Mirror DUT's integer math (32-bit signed, truncation semantics)
  function automatic signed [31:0] abs_i32 (input signed [31:0] a);
    abs_i32 = (a >= 0) ? a : -a;
  endfunction

  function automatic signed [31:0] pow2_i32 (input signed [31:0] a);
    logic signed [63:0] prod;
    begin
      prod     = a * a;           // 64-bit product
      pow2_i32 = prod[31:0];      // truncate to 32-bit like DUT's integer
    end
  endfunction

  // Static param sanity
  initial begin
    assert (SCALE >= 0 && SCALE < 32)
      else $fatal(1, "SCALE out of range: %0d", SCALE);
  end

  // Main functional check and targeted coverage (immediate, no clock required)
  always_comb begin
    // Inputs must be known
    assert (!$isunknown({x1,y1,z1,x2,y2,z2}))
      else $error("X/Z on inputs");

    // Compute expected result with DUT-accurate casting/truncation and unsigned accumulation
    automatic logic signed [32:0] dx33 = $signed(x2) - $signed(x1);
    automatic logic signed [32:0] dy33 = $signed(y2) - $signed(y1);
    automatic logic signed [32:0] dz33 = $signed(z2) - $signed(z1);

    automatic logic signed [31:0] dx = dx33[31:0];
    automatic logic signed [31:0] dy = dy33[31:0];
    automatic logic signed [31:0] dz = dz33[31:0];

    automatic logic signed [31:0] ax = abs_i32(dx);
    automatic logic signed [31:0] ay = abs_i32(dy);
    automatic logic signed [31:0] az = abs_i32(dz);

    automatic logic signed [31:0] px = pow2_i32(ax);
    automatic logic signed [31:0] py = pow2_i32(ay);
    automatic logic signed [31:0] pz = pow2_i32(az);

    automatic logic [31:0] sum = 32'd0;
    sum = sum + logic'(px);  // unsigned 32-bit accumulation
    sum = sum + logic'(py);
    sum = sum + logic'(pz);

    automatic logic [31:0] exp = (sum >> SCALE); // logical shift like DUT

    // Functional equivalence
    assert (distance === exp)
      else $error("distance mismatch: exp=%0h got=%0h", exp, distance);

    // Output must be known when inputs are known
    assert (!$isunknown(distance))
      else $error("X/Z on distance with known inputs");

    // Trivial identity: equal points -> zero
    assert ( ((x1===x2)&&(y1===y2)&&(z1===z2)) -> (distance===32'd0) )
      else $error("Nonzero distance when points equal");

    // Targeted coverage (immediate cover)
    cover ( (x1===x2)&&(y1===y2)&&(z1===z2) && distance==32'd0 );            // equal points
    cover ( (x1!=x2)&&(y1===y2)&&(z1===z2) );                                 // delta only in X
    cover ( (x1===x2)&&(y1!=y2)&&(z1===z2) );                                 // delta only in Y
    cover ( (x1===x2)&&(y1===y2)&&(z1!=z2) );                                 // delta only in Z
    cover ( ax==32'sd0 || ay==32'sd0 || az==32'sd0 );                         // zero-axis deltas
    cover ( ax==32'sd1 || ay==32'sd1 || az==32'sd1 );                         // small deltas
    cover ( ax==32'sd65536 || ay==32'sd65536 || az==32'sd65536 );             // pow2 truncates to zero
    cover ( dx==32'sh8000_0000 || dy==32'sh8000_0000 || dz==32'sh8000_0000 ); // abs overflow corner
  end

endmodule

// Bind the checker to the DUT
bind distance_calculator distance_calculator_sva #(.SCALE(16)) distance_calculator_sva_i (.*);