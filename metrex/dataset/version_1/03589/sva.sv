// SVA checker for mux_16to1
// Bind into DUT: bind mux_16to1 mux_16to1_sva u_mux_16to1_sva(.*);

module mux_16to1_sva (
  input  logic [15:0] in0,
  input  logic [15:0] in1,
  input  logic [15:0] in2,
  input  logic [15:0] in3,
  input  logic [15:0] in4,
  input  logic [15:0] in5,
  input  logic [15:0] in6,
  input  logic [15:0] in7,
  input  logic [15:0] in8,
  input  logic [15:0] in9,
  input  logic [15:0] in10,
  input  logic [15:0] in11,
  input  logic [15:0] in12,
  input  logic [15:0] in13,
  input  logic [15:0] in14,
  input  logic [15:0] in15,
  input  logic [4:0]  sel,
  input  logic [31:0] out
);

  // Golden model (zero-extended 16->32)
  function automatic logic [31:0] exp_out(
    input logic [4:0]  s,
    input logic [15:0] i0,  input logic [15:0] i1,
    input logic [15:0] i2,  input logic [15:0] i3,
    input logic [15:0] i4,  input logic [15:0] i5,
    input logic [15:0] i6,  input logic [15:0] i7,
    input logic [15:0] i8,  input logic [15:0] i9,
    input logic [15:0] i10, input logic [15:0] i11,
    input logic [15:0] i12, input logic [15:0] i13,
    input logic [15:0] i14, input logic [15:0] i15
  );
    unique case (s)
      5'd0:  exp_out = {16'h0000, i0};
      5'd1:  exp_out = {16'h0000, i1};
      5'd2:  exp_out = {16'h0000, i2};
      5'd3:  exp_out = {16'h0000, i3};
      5'd4:  exp_out = {16'h0000, i4};
      5'd5:  exp_out = {16'h0000, i5};
      5'd6:  exp_out = {16'h0000, i6};
      5'd7:  exp_out = {16'h0000, i7};
      5'd8:  exp_out = {16'h0000, i8};
      5'd9:  exp_out = {16'h0000, i9};
      5'd10: exp_out = {16'h0000, i10};
      5'd11: exp_out = {16'h0000, i11};
      5'd12: exp_out = {16'h0000, i12};
      5'd13: exp_out = {16'h0000, i13};
      5'd14: exp_out = {16'h0000, i14};
      5'd15: exp_out = {16'h0000, i15};
      default: exp_out = 32'h0000_0000;
    endcase
  endfunction

  // Combinational, immediate checks and coverage
  always_comb begin
    logic [31:0] e = exp_out(sel,in0,in1,in2,in3,in4,in5,in6,in7,in8,in9,in10,in11,in12,in13,in14,in15);

    // Functional equivalence
    assert (out === e)
      else $error("mux_16to1: out mismatch for sel=%0d", sel);

    // Zero-extension must always hold
    assert (out[31:16] === 16'h0000)
      else $error("mux_16to1: upper bits not zero-extended");

    // Avoid X/Z on select (prevents X-masking via default)
    assert (!$isunknown(sel))
      else $error("mux_16to1: sel contains X/Z");

    // Coverage: hit every select and the default range
    cover (sel == 5'd0);
    cover (sel == 5'd1);
    cover (sel == 5'd2);
    cover (sel == 5'd3);
    cover (sel == 5'd4);
    cover (sel == 5'd5);
    cover (sel == 5'd6);
    cover (sel == 5'd7);
    cover (sel == 5'd8);
    cover (sel == 5'd9);
    cover (sel == 5'd10);
    cover (sel == 5'd11);
    cover (sel == 5'd12);
    cover (sel == 5'd13);
    cover (sel == 5'd14);
    cover (sel == 5'd15);
    cover (sel > 5'd15); // default branch

    // Sanity covers tying data to output on a couple of selects
    cover (sel == 5'd0  && out[15:0] === in0);
    cover (sel == 5'd15 && out[15:0] === in15);
  end

endmodule

// Suggested bind
// bind mux_16to1 mux_16to1_sva u_mux_16to1_sva(.*);