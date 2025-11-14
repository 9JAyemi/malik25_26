// SVA package for nand_gate_pipeline + decoder_2to4 + top_module
// Focused, concise checks and coverage. Bind these into the DUT.

//////////////////////////////////////////////////////////////
// Assertions for nand_gate_pipeline
//////////////////////////////////////////////////////////////
module nand_gate_pipeline_sva (
  input logic a,
  input logic b,
  input logic out,
  input logic [1:0] stage1,
  input logic stage2
);
  // Functional spec: NAND with 1 time-unit latency
  always @(a or b) begin
    #1 assert (out === ~(a & b))
       else $error("nand_gate_pipeline: out != ~(a&b) after 1t");
    // Internal stage intent at 1t
    #1 assert (stage2 === (a & b))
       else $error("nand_gate_pipeline: stage2 != (a&b) after 1t");
    #1 assert (stage1[1] === ~(a & b))
       else $error("nand_gate_pipeline: stage1[1] != ~(a&b) after 1t");
    // No X/Z after settle
    #1 assert (!$isunknown({stage1,stage2,out}))
       else $error("nand_gate_pipeline: X/Z detected after 1t");
  end

  // Input combination coverage
  cover property (@(posedge a or negedge a or posedge b or negedge b) {a,b}==2'b00);
  cover property (@(posedge a or negedge a or posedge b or negedge b) {a,b}==2'b01);
  cover property (@(posedge a or negedge a or posedge b or negedge b) {a,b}==2'b10);
  cover property (@(posedge a or negedge a or posedge b or negedge b) {a,b}==2'b11);
endmodule

bind nand_gate_pipeline nand_gate_pipeline_sva
  (.a(a), .b(b), .out(out), .stage1(stage1), .stage2(stage2));

//////////////////////////////////////////////////////////////
// Assertions for decoder_2to4
//////////////////////////////////////////////////////////////
module decoder_2to4_sva (
  input  logic [1:0] in,
  input  logic [3:0] out,
  input  logic nand1,
  input  logic nand2,
  input  logic nand3,
  input  logic nand4
);
  // Check internal NAND term correctness at 1t after input change
  always @(in) begin
    #1 assert (nand1 === ~( in[0]  &  in[1])) else $error("decoder: nand1 wrong @1t");
    #1 assert (nand2 === ~(~in[0]  &  in[1])) else $error("decoder: nand2 wrong @1t");
    #1 assert (nand3 === ~( in[0]  & ~in[1])) else $error("decoder: nand3 wrong @1t");
    #1 assert (nand4 === ~(~in[0]  & ~in[1])) else $error("decoder: nand4 wrong @1t");
  end

  // Functional spec: active-low one-hot with 2t total latency (NAND + output reg)
  function automatic logic [3:0] exp_out(input logic [1:0] vin);
    case (vin)
      2'b00: exp_out = 4'b1110; // only out[3] low
      2'b01: exp_out = 4'b1101; // only out[2] low
      2'b10: exp_out = 4'b1011; // only out[1] low
      default: exp_out = 4'b0111; // only out[0] low
    endcase
  endfunction

  always @(in) begin
    #2 assert (out === exp_out(in))
       else $error("decoder: out mismatch exp_out(in) @2t");
    #2 assert ($onehot(~out))
       else $error("decoder: ~out not one-hot @2t");
    #2 assert (!$isunknown(out))
       else $error("decoder: X/Z on out @2t");
  end

  // Coverage: all input cases seen, and each output bit asserted low at least once
  cover property (@(in) in==2'b00);
  cover property (@(in) in==2'b01);
  cover property (@(in) in==2'b10);
  cover property (@(in) in==2'b11);
  cover property (@(posedge out[0] or negedge out[0]) out[0]==1'b0);
  cover property (@(posedge out[1] or negedge out[1]) out[1]==1'b0);
  cover property (@(posedge out[2] or negedge out[2]) out[2]==1'b0);
  cover property (@(posedge out[3] or negedge out[3]) out[3]==1'b0);
endmodule

bind decoder_2to4 decoder_2to4_sva
  (.in(in), .out(out), .nand1(nand1), .nand2(nand2), .nand3(nand3), .nand4(nand4));

//////////////////////////////////////////////////////////////
// End-to-end checks at top_module
//////////////////////////////////////////////////////////////
module top_module_sva (
  input  logic a,
  input  logic b,
  input  logic [3:0] out
);
  function automatic logic [3:0] exp_out(input logic va, vb);
    case ({va,vb})
      2'b00: exp_out = 4'b1110;
      2'b01: exp_out = 4'b1101;
      2'b10: exp_out = 4'b1011;
      default: exp_out = 4'b0111;
    endcase
  endfunction

  // Expect 2t total latency from a/b change to final out
  always @(a or b) begin
    #2 assert (out === exp_out(a,b))
       else $error("top: out != expected @2t from a/b change");
    #2 assert ($onehot(~out))
       else $error("top: not one-hot-low @2t");
  end
endmodule

bind top_module top_module_sva
  (.a(a), .b(b), .out(out));