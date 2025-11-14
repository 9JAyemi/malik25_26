// SVA for signed_multiplier
// Concise, high-quality checks + essential functional coverage

module signed_multiplier_sva #(parameter W=8) (
  input  logic                 clk,
  input  logic                 reset,
  input  logic signed [W-1:0]  in1,
  input  logic signed [W-1:0]  in2,
  input  logic signed [2*W-1:0] out
);
  // Handy constants
  localparam logic signed [W-1:0] MAXP = $signed((1<<(W-1)) - 1); // +127 for W=8
  localparam logic signed [W-1:0] MINN = $signed(1<<(W-1));       // -128 for W=8

  // Core functional correctness (zero-latency, signed multiply)
  assert property (@(posedge clk) disable iff (reset)
    out == $signed(in1) * $signed(in2)
  );

  // No X/Z on output when inputs are known
  assert property (@(posedge clk) disable iff (reset)
    !$isunknown({in1,in2}) |-> !$isunknown(out)
  );

  // Algebraic identities
  assert property (@(posedge clk) disable iff (reset)
    (in1==0 || in2==0) |-> (out==0)
  );
  assert property (@(posedge clk) disable iff (reset)
    (in2==1) |-> (out==in1)
  );
  assert property (@(posedge clk) disable iff (reset)
    (in1==1) |-> (out==in2)
  );
  assert property (@(posedge clk) disable iff (reset)
    (in2==-1) |-> (out==-in1)
  );
  assert property (@(posedge clk) disable iff (reset)
    (in1==-1) |-> (out==-in2)
  );

  // Sign rule for non-zero operands
  assert property (@(posedge clk) disable iff (reset)
    (in1!=0 && in2!=0) |-> (out[2*W-1] == (in1[W-1] ^ in2[W-1]))
  );

  // Functional coverage (corner cases, signs, extremes)
  cover property (@(posedge clk) disable iff (reset) (in1>0  && in2>0  && out>0 ));
  cover property (@(posedge clk) disable iff (reset) (in1>0  && in2<0  && out<0 ));
  cover property (@(posedge clk) disable iff (reset) (in1<0  && in2>0  && out<0 ));
  cover property (@(posedge clk) disable iff (reset) (in1<0  && in2<0  && out>0 ));

  cover property (@(posedge clk) disable iff (reset) (in1==0 || in2==0));
  cover property (@(posedge clk) disable iff (reset) (in1==1 || in2==1));
  cover property (@(posedge clk) disable iff (reset) (in1==-1 || in2==-1));

  cover property (@(posedge clk) disable iff (reset) (in1==MAXP && in2==MAXP)); // 127*127
  cover property (@(posedge clk) disable iff (reset) (in1==MINN && in2==MAXP)); // -128*127
  cover property (@(posedge clk) disable iff (reset) (in1==MINN && in2==MINN)); // -128*-128
endmodule

// Bind into DUT
bind signed_multiplier signed_multiplier_sva #(.W(8)) sva_i (
  .clk(clk),
  .reset(reset),
  .in1(in1),
  .in2(in2),
  .out(out)
);