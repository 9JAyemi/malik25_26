// SVA checkers + bind statements

// ---------------- addsub_16bit ----------------
module addsub_16bit_sva(
  input logic [15:0] in0, in1,
  input logic        control,
  input logic [15:0] out
);
  // Functional correctness (blocking assignments -> ##0)
  property p_add; @(in0 or in1 or control or out) control |-> ##0 (out == (in0 + in1)); endproperty
  property p_sub; @(in0 or in1 or control or out) !control |-> ##0 (out == (in0 - in1)); endproperty
  assert property (p_add);
  assert property (p_sub);

  // Knownness
  assert property (@(in0 or in1 or control or out) (!$isunknown({in0,in1,control})) |-> ##0 !$isunknown(out));

  // Coverage
  cover property (@(in0 or in1 or control) control);
  cover property (@(in0 or in1 or control) !control);
  cover property (@(in0 or in1 or control) control && ({1'b0,in0}+{1'b0,in1})[16]); // add overflow
  cover property (@(in0 or in1 or control) !control && (in0 < in1));                // sub borrow
endmodule

bind addsub_16bit addsub_16bit_sva i_addsub_16bit_sva(.in0(in0), .in1(in1), .control(control), .out(out));


// ---------------- comparator_4bit ----------------
module comparator_4bit_sva(
  input logic [3:0] in0, in1,
  input logic [3:0] out
);
  // Encoding correctness (blocking assignments -> ##0)
  assert property (@(in0 or in1 or out) (in0 > in1) |-> ##0 (out == 4'b0001));
  assert property (@(in0 or in1 or out) (in0 < in1) |-> ##0 (out == 4'b0010));
  assert property (@(in0 or in1 or out) (in0 == in1) |-> ##0 (out == 4'b0111));

  // Only legal encodings
  assert property (@(in0 or in1 or out) out inside {4'b0001,4'b0010,4'b0111});

  // Knownness
  assert property (@(in0 or in1 or out) (!$isunknown({in0,in1})) |-> ##0 !$isunknown(out));

  // Coverage
  cover property (@(in0 or in1) (in0 > in1));
  cover property (@(in0 or in1) (in0 < in1));
  cover property (@(in0 or in1) (in0 == in1));
endmodule

bind comparator_4bit comparator_4bit_sva i_comparator_4bit_sva(.in0(in0), .in1(in1), .out(out));


// ---------------- top_module ----------------
module top_module_sva(
  input  logic [15:0] in0, in1,
  input  logic        control,
  input  logic [15:0] addsub_out,
  input  logic [3:0]  comp_out,
  input  logic [1:0]  OUT
);
  // Mapping from comparator encoding to OUT (NBA used in DUT -> ##1)
  assert property (@(addsub_out or comp_out) (comp_out == 4'b0001) |-> ##1 (OUT == 2'b01));
  assert property (@(addsub_out or comp_out) (comp_out == 4'b0010) |-> ##1 (OUT == 2'b10));
  assert property (@(addsub_out or comp_out) (comp_out == 4'b0111) |-> ##1 (OUT == 2'b11));

  // OUT only legal values
  assert property (@(addsub_out or comp_out or OUT) OUT inside {2'b01,2'b10,2'b11});

  // End-to-end check independent of comp_out (NBA -> ##1)
  assert property (@(addsub_out or comp_out)
                   (addsub_out[3:0] >  in0[3:0]) |-> ##1 (OUT == 2'b01));
  assert property (@(addsub_out or comp_out)
                   (addsub_out[3:0] <  in0[3:0]) |-> ##1 (OUT == 2'b10));
  assert property (@(addsub_out or comp_out)
                   (addsub_out[3:0] == in0[3:0]) |-> ##1 (OUT == 2'b11));

  // Knownness
  assert property (@(addsub_out or comp_out)
                   (!$isunknown({addsub_out[3:0], in0[3:0], comp_out})) |-> ##1 !$isunknown(OUT));

  // Coverage: all OUT encodings and operation modes exercised
  cover property (@(addsub_out or comp_out) OUT == 2'b01);
  cover property (@(addsub_out or comp_out) OUT == 2'b10);
  cover property (@(addsub_out or comp_out) OUT == 2'b11);

  // Cross operation mode vs compare outcome
  cover property (@(addsub_out or comp_out)  control && (addsub_out[3:0] >  in0[3:0]) && ##1 (OUT==2'b01));
  cover property (@(addsub_out or comp_out)  control && (addsub_out[3:0] <  in0[3:0]) && ##1 (OUT==2'b10));
  cover property (@(addsub_out or comp_out)  control && (addsub_out[3:0] == in0[3:0]) && ##1 (OUT==2'b11));
  cover property (@(addsub_out or comp_out) !control && (addsub_out[3:0] >  in0[3:0]) && ##1 (OUT==2'b01));
  cover property (@(addsub_out or comp_out) !control && (addsub_out[3:0] <  in0[3:0]) && ##1 (OUT==2'b10));
  cover property (@(addsub_out or comp_out) !control && (addsub_out[3:0] == in0[3:0]) && ##1 (OUT==2'b11));
endmodule

bind top_module top_module_sva i_top_module_sva(
  .in0(in0), .in1(in1), .control(control),
  .addsub_out(addsub_out), .comp_out(comp_out), .OUT(OUT)
);