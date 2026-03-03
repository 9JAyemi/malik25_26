// SVA for zero_to_one_counter
module sva_zero_to_one_counter (
  input logic clk,
  input logic reset,
  input logic [15:0] in,
  input logic out
);
  default clocking @(posedge clk); endclocking

  // Knownness
  assert property (disable iff (reset) !$isunknown(out));

  // Next-state functional checks (use $past to avoid NBA race)
  assert property ($past(reset) |-> out == 1'b0);
  assert property ($past(!reset && in == 16'hFFFF) |-> out == 1'b1);
  assert property ($past(!reset && in != 16'hFFFF) |-> out == ~$past(out));

  // Covers
  cover property ($past(!reset && in != 16'hFFFF && $past(out)==1'b0) && out==1'b1); // 0->1 toggle
  cover property ($past(!reset && in != 16'hFFFF && $past(out)==1'b1) && out==1'b0); // 1->0 toggle
  cover property ($past(!reset && in == 16'hFFFF) && out==1'b1);                     // force-1 path
  cover property ($rose(reset));                                                     // see reset happen
endmodule

// SVA for adder_4bit_cin_cout (combinational)
module sva_adder_4bit_cin_cout (
  input  logic [3:0] A,
  input  logic [3:0] B,
  input  logic       CIN,
  input  logic [3:0] S,
  input  logic       COUT
);
  // Functional equivalence
  assert property ( {COUT,S} == (A + B + CIN) );

  // Knownness propagation: known inputs imply known outputs
  assert property ( (!$isunknown({A,B,CIN})) |-> (!$isunknown({S,COUT})) );

  // Covers
  cover property (CIN==1'b0 && COUT==1'b1); // carry generated
  cover property (CIN==1'b1 && COUT==1'b1); // carry with CIN
  cover property (S==4'h0);                 // sum wrap to 0
endmodule

// SVA for top_module
module sva_top_module (
  input  logic        clk,
  input  logic        reset,
  input  logic [3:0]  A,
  input  logic [3:0]  B,
  input  logic        CIN,
  input  logic [15:0] in,
  input  logic [3:0]  S,
  input  logic        zero_to_one_out
);
  default clocking @(posedge clk); endclocking

  // Top-level functional relationship holds at all times
  assert property ( S == (A + B + CIN + zero_to_one_out)[3:0] );

  // Knownness: known inputs imply known S
  assert property ( (!$isunknown({A,B,CIN,zero_to_one_out})) |-> (!$isunknown(S)) );

  // Covers
  // - S toggles when adder inputs are stable and counter path is in toggle mode
  cover property ( $stable(A) && $stable(B) && $stable(CIN) &&
                   $past(!reset && in!=16'hFFFF) && (!reset && in!=16'hFFFF) &&
                   (S != $past(S)) );

  // - Wrap-around at 0xF + carry-in from counter
  cover property ( (((A + B + CIN) & 4'hF) == 4'hF) && zero_to_one_out==1'b1 && S==4'h0 );

  // - Force-one from counter affects S
  cover property ( $past(!reset && in==16'hFFFF) && (S == (A + B + CIN + 1)[3:0]) );
endmodule

// Bind the SVA to the DUTs
bind zero_to_one_counter     sva_zero_to_one_counter z2o_sva   (.clk(clk), .reset(reset), .in(in), .out(out));
bind adder_4bit_cin_cout     sva_adder_4bit_cin_cout add_sva   (.A(A), .B(B), .CIN(CIN), .S(S), .COUT(COUT));
bind top_module              sva_top_module          top_sva   (.clk(clk), .reset(reset), .A(A), .B(B), .CIN(CIN), .in(in), .S(S), .zero_to_one_out(zero_to_one_out));