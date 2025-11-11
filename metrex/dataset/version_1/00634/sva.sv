// SVA checker for top_module (combinational, race-safe with #0)
// Bind this to your DUT: bind top_module top_module_sva sva(.in(in), .in1_hi(in1_hi), .in1_lo(in1_lo), .in2_hi(in2_hi), .in2_lo(in2_lo), .out(out));

module top_module_sva (
  input logic [15:0] in,
  input logic [3:0]  in1_hi, in1_lo,
  input logic [3:0]  in2_hi, in2_lo,
  input logic [7:0]  out
);

  function automatic logic [3:0] abs4(input logic [3:0] a, b);
    abs4 = (a >= b) ? (a - b) : (b - a);
  endfunction

  logic [7:0] expect_out;

  always_comb begin
    #0; // let combinational logic settle

    // Structural slice checks
    assert (in1_hi == in[15:12]) else $error("in1_hi mismatch: %h vs %h", in1_hi, in[15:12]);
    assert (in1_lo == in[11:8])  else $error("in1_lo mismatch: %h vs %h", in1_lo, in[11:8]);
    assert (in2_hi == in[7:4])   else $error("in2_hi mismatch: %h vs %h", in2_hi, in[7:4]);
    assert (in2_lo == in[3:0])   else $error("in2_lo mismatch: %h vs %h", in2_lo, in[3:0]);

    // Functional ABS sum check
    expect_out = abs4(in1_hi, in2_hi) + abs4(in1_lo, in2_lo);
    assert (out == expect_out) else
      $error("out mismatch: got %0d exp %0d (|%0d-%0d|+|%0d-%0d|)", out, expect_out, in1_hi, in2_hi, in1_lo, in2_lo);

    // Range check (max 15+15)
    assert (out <= 8'd30) else $error("out out-of-range: %0d", out);

    // Degenerate cases
    if (in1_hi == in2_hi) assert (out == abs4(in1_lo, in2_lo)) else $error("hi equal but out != |lo diff|");
    if (in1_lo == in2_lo) assert (out == abs4(in1_hi, in2_hi)) else $error("lo equal but out != |hi diff|");
    if ((in1_hi == in2_hi) && (in1_lo == in2_lo)) assert (out == 8'd0) else $error("all equal but out != 0");

    // X-propagation sanity: if inputs are 2-state, outputs must be 2-state
    if (!$isunknown(in)) assert (!$isunknown({in1_hi,in1_lo,in2_hi,in2_lo,out})) else
      $error("Outputs contain X/Z with 2-state input");

    // Functional coverage
    cover (in1_hi >  in2_hi);
    cover (in1_hi <  in2_hi);
    cover (in1_hi == in2_hi);
    cover (in1_lo >  in2_lo);
    cover (in1_lo <  in2_lo);
    cover (in1_lo == in2_lo);
    cover (out == 8'd0);
    cover (out == 8'd15);
    cover (out == 8'd30);
  end

endmodule

// Example bind (place in a separate file/package as needed)
// bind top_module top_module_sva sva(.in(in), .in1_hi(in1_hi), .in1_lo(in1_lo), .in2_hi(in2_hi), .in2_lo(in2_lo), .out(out));